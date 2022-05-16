open Ast
open List_code
open Queue_code
open Map_code
open Network_util_code
open One_server_network_code

type 'a logTy =
  'a requestTy alist
type 'a client_tableTy =
  (saddr, int * (unit, 'a option) sumTy option) amap Atomic.t
type 'a databaseTy =
  ((string, 'a) amap) Atomic.t


let emit_reply lk (outQ : 'a replyTy queue Atomic.t) (reply : 'a replyTy) =
  acquire lk;
  outQ := queue_add reply !outQ;
  release lk

let commit_op
    (ctable : 'a client_tableTy)
    (db : 'a databaseTy)
    (req : 'a requestTy) : 'a replyTy =
  let ((rop, rid), caddr) = req in
  (* Process the request *)
  let res =
    match rop with
    | InjL p ->                 (* write value v to the key k *)
      let (k, v) = p in
      db := map_insert k v !db;
      InjL ()
    | InjR k ->
      InjR (map_lookup k !db)    (* read the key k *)
  in
  ctable := map_insert caddr (rid, Some res) !ctable ;
  ((res, rid), caddr)

let process_new_request lk log ctable db outQ req =
  let ((_rop, rid), caddr) = req in
  ctable := map_insert caddr (rid, None) !ctable;
  log := list_append !log (list_cons req list_nil);
  let reply = commit_op ctable db req in
  emit_reply lk outQ reply

let process_request
    (log : 'a logTy Atomic.t)
    (ctable : 'a client_tableTy)
    (db :'a databaseTy)
    (lk : Mutex.t)
    (outQ : 'a replyTy queue Atomic.t)
    (req : 'a requestTy)
  =
  let ((_rop, rid), caddr) = req in
  match map_lookup caddr !ctable with
    None -> (* New client *)
    process_new_request lk log ctable db outQ req
  | Some p ->
    let (t, ro) = p in
    if rid < t then () (* Ignore stale requests. *)
    else
      match ro with
      (* If no data associated, then the request must be pending
         in which case the duplicate request can be ignored. *)
        None -> assert (rid = t)
      (* Here we know that the last client's request has been processed. *)
      (* We assume each client can have only one oustanding request,
         and that the server does not crashes. Therefore, the client
         can only send a request with a seqid at most one greather
         than what is stored at the server. *)
      | Some res ->
        (* If the same request, just resend the acknowledgement *)
        if rid = t then emit_reply lk outQ ((res, rid), caddr)
        else
          begin
            assert (rid = t + 1);
            process_new_request lk log ctable db outQ req
          end


let fetch_request (lk : Mutex.t) (inQ : 'a queue Atomic.t) =
    acquire lk;
    let tmp = !inQ in
    if not (queue_is_empty tmp)
    then
      begin
        let q = unSOME (queue_take_opt tmp) in
        let (hd, tl) = q in
        ignore(inQ := tl);
        release lk;
        Some hd
      end
    else None

let request_loop
    (log : 'a logTy Atomic.t) (ctable : 'a client_tableTy)
    (db :'a databaseTy)
    (lk : Mutex.t)
    (inQ : 'a requestTy queue Atomic.t)
    (outQ : 'a replyTy queue Atomic.t) =
  let rec loop () : unit =
    let req_opt = fetch_request lk inQ in
    match req_opt with
    | None -> unsafe (fun () -> Unix.sleepf 0.5); loop ()
    | Some req ->
      process_request log ctable db lk outQ req;
      loop ()
  in loop ()

let init_server (val_ser[@metavar]) srv =
      (* the log of received requests so far in a global order *)
    let log = ref list_nil in
    (* the table with the most recent request info for each client *)
    (* client table : caddr -> (seqid, pending|processed reqest) *)
    let (ctable : 'a client_tableTy) = ref (map_empty ()) in
    (* --- a specific service the key-value store --- *)
    let db = ref (map_empty ()) in
    (* ------------- network communication layer  ------------- *)
    let netdata = init_network val_ser srv in
    let ((lk, inQ), outQ) = netdata in
    (* -------------------- request loop ------------------------ *)
    request_loop log ctable db lk inQ outQ
