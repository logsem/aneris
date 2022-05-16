open Ast
open Queue_code
open Map_code
open Network_util_code
open Client_server_code
open Ddb_serialization_code

let process_request
    (db :  'a databaseTy Atomic.t)
    (lkOut : Mutex.t)
    (qOut : 'a replyEventTy queue Atomic.t)
    (req_ev : 'a requestEventTy) =
  let (req, chan) = req_ev in
  let (res : 'a replyTy) =
    match req with
    | InjL p ->                 (* write value v to the key k *)
      let (k, v) = p in
      db := map_insert k v !db;
      InjL ()
    | InjR k ->
      InjR (map_lookup k !db)    (* read the key k *)
  in
  acquire lkOut;
  qOut := queue_add (res, chan) !qOut;
  release lkOut

let fetch_from_queue (lk : Mutex.t) (q : 'a queue Atomic.t) : 'a option =
  acquire lk;
  let tmp = !q in
  if not (queue_is_empty tmp)
  then
    begin
      let qu = unSOME (queue_take_opt tmp) in
      let (hd, tl) = qu in
      ignore (q := tl);
      release lk;
      Some hd
    end
  else None


let request_loop
    (db :'a databaseTy Atomic.t)
    (lkIn : Mutex.t)
    (lkOut : Mutex.t)
    (qIn : 'a requestEventTy queue Atomic.t)
    (qOut : 'a replyEventTy queue Atomic.t) =
  let rec loop () : unit =
    let req_opt = fetch_from_queue lkIn qIn in
    match req_opt with
    | None -> unsafe (fun () -> Unix.sleepf 0.5); loop ()
    | Some req ->
      process_request db lkOut qOut req;
      loop ()
  in loop ()


let recv_from_chan_loop
    (c : 'a db_chan_descr)
    (lkIn : Mutex.t)
    (qIn : 'a requestEventTy queue Atomic.t) : unit =
  let rec loop () =
    let (req : 'a requestTy) = recv c in
    acquire lkIn;
    qIn := queue_add (req, c) !qIn;
    release lkIn;
    loop ()
  in loop ()

let send_loop (lkOut : Mutex.t) (qOut :'a replyEventTy queue Atomic.t) : unit =
  let rec loop () =
    let reply_opt = fetch_from_queue lkOut qOut in
    match reply_opt with
    | None -> unsafe (fun () -> Unix.sleepf 0.5); loop ()
    | Some ev ->
      let (repl, ch) = ev in
      fork (send ch) repl;
      loop ()
  in loop ()

let accept_new_connections_loop
    (skt : ('a replyTy, 'a requestTy) server_skt)
    (lkIn : Mutex.t)
    (qIn : 'a requestEventTy queue Atomic.t) =
  let rec loop () =
    let new_conn = accept skt in
    let (clt_chan, _clt_addr) = new_conn in
    fork (recv_from_chan_loop clt_chan lkIn) qIn;
    loop ()
  in loop ()

let init_server (val_ser[@metavar] : 'a serializer) (srv_addr : saddr) : unit =
  let (db : 'a databaseTy Atomic.t) = ref (map_empty ()) in
  let (skt : ('a replyTy,'b requestTy) server_skt) =
    make_server_skt
      (reply_serializer val_ser)
      (request_serializer val_ser)
      srv_addr in
  let (qIn : 'a requestEventTy queue Atomic.t) = ref (queue_empty ()) in
  let (qOut : 'a replyEventTy queue Atomic.t) = ref (queue_empty ()) in
  let lkIn = newlock () in
  let lkOut = newlock () in
  fork (send_loop lkOut) qOut;
  server_listen skt;
  fork (accept_new_connections_loop skt lkIn) qIn;
  fork (request_loop db lkIn lkOut qIn) qOut


(** Simple database implementation with stop-and-wait requests *)
let request ch lk req =
  (* Use lock to prevent client to run requests in parallel. *)
  acquire lk;
  send ch req;
  let msg = recv ch in
  release lk;
  msg

let install_proxy (val_ser[@metavar]) clt_addr srv_addr =
  let skt = make_client_skt
      (request_serializer val_ser)
      (reply_serializer val_ser)
      clt_addr in
  let ch = connect skt srv_addr in
  let lk = newlock () in
  let write k v =
    match request ch lk (InjL (k, v)) with
    | InjL _u -> ()
    | InjR _abs -> assert false in
  let read k  =
    match request ch lk (InjR k) with
    | InjL _abs -> assert false
    | InjR r -> r
  in (write, read)
