open Ast
open List_code
open Queue_code
open Map_code
open Network_util_code
open Serialization_code
open Client_server_code

(* -------------------------------------------------------------------------- *)
(** Serializers *)
(* -------------------------------------------------------------------------- *)

let write_serializer (val_ser[@metavar]) =
  prod_serializer string_serializer val_ser

let read_serializer = string_serializer

(* ⟨CLIENT-LEADER-REQUEST (WRITE|READ)⟩ *)
let req_c2l_ser (val_ser[@metavar]) =
  (sum_serializer (write_serializer val_ser) read_serializer)

(* ⟨LEADER-CLIENT-REPLY (WRITE|READ)⟩ *)
let rep_l2c_ser (val_ser[@metavar]) =
  (sum_serializer (unit_serializer) (option_serializer val_ser))

(* ⟨FOLLOWER-LEADER-REQUEST int⟩ *)
let req_f2l_ser = int_serializer

(* ⟨LEADER-FOLLOWER-REPLY (req, int)⟩ *)
let rep_l2f_ser (val_ser[@metavar]) =
  prod_serializer (prod_serializer string_serializer val_ser) int_serializer

(* ⟨CLIENT-FOLLOWER-REQUEST (READ-ONLY)⟩ *)
let req_c2f_ser = read_serializer

(* ⟨FOLLOWER-CLIENT-REPLY (READ-ONLY)⟩ *)
let rep_f2c_ser (val_ser[@metavar]) =  option_serializer val_ser

(* -------------------------------------------------------------------------- *)
(** Type definitions *)
(* -------------------------------------------------------------------------- *)

type 'a wr_reqTy = string * 'a
type 'a reqTy = ('a wr_reqTy, string) sumTy
type 'a repTy = (unit, 'a option) sumTy
type 'a db_chan = ('a repTy, 'a reqTy) chan_descr
type 'a mcell = monitor * 'a option Atomic.t
type 'a reqEvTy = 'a reqTy * 'a repTy mcell
type 'a rd_reqEvTy = string * 'a option mcell

type 'a dbTy = ((string, 'a) amap)
type 'a mqueue = monitor * 'a queue Atomic.t
type 'a log_entry = ('a wr_reqTy * int)
type 'a log =  ('a log_entry alist * int) Atomic.t
type 'a mlog =  monitor * 'a log

(* -------------------------------------------------------------------------- *)
(** Monitored containers *)
(* -------------------------------------------------------------------------- *)

let mcell_create () : 'a mcell =
  let mon = new_monitor () in
  let cell = ref None in
  (mon, cell)

(** Assumes holding lock. Holds the lock at return. *)
let mcell_wait_some (mc : 'a mcell) : unit =
  let (m, c) = mc in
  let rec aux () =
    match !c with
    | None -> monitor_wait m; aux ()
    | Some _v -> ()
  in aux ()

(** Assumes holding lock. Holds the lock at return. *)
let mcell_wait_none (mc : 'a mcell) : unit =
  let (m, c) = mc in
  let rec aux () =
    match !c with
    | None -> ()
    | Some _v -> monitor_wait m; aux ()
  in aux ()

let mcell_set (mc : 'a mcell) (x : 'a) : unit =
  let (m, c) = mc in
  monitor_acquire m;
  mcell_wait_none mc;
  c := Some x;
  monitor_signal m;
  monitor_release m

(** Assumes holding lock. Holds the lock at return. *)
let mcell_fetch (mc : 'a mcell) : 'a =
  let (m, c) = mc in
  monitor_acquire m;
  mcell_wait_some mc;
  let rep = unSOME !c in
  ignore (c := None);
  monitor_signal m;
  monitor_release m;
  rep

let mqueue_create () : 'a mqueue =
  let mon = new_monitor () in
  let que = ref (queue_empty ()) in
  (mon, que)

let mqueue_wait (mq : 'a mqueue) : unit =
  let (m, q) = mq in
  let rec aux () =
    if queue_is_empty !q
    then (monitor_wait m; aux ())
    else ()
  in aux ()

let mqueue_fetch (mq : 'a mqueue) : 'a =
  let (m, q) = mq in
  monitor_acquire m;
  mqueue_wait mq;
  let tmp = !q in
  let qu = unSOME (queue_take_opt tmp) in
  let (hd, tl) = qu in
  ignore (q := tl);
  monitor_release m;
  hd

(* TODO: add mqueue_take_opt, if needed. *)
let mqueue_add (mq : 'a mqueue) (x : 'a) : unit =
  let (m, q) = mq in
  monitor_acquire m;
  q := queue_add x !q;
  monitor_broadcast m;
  monitor_release m

(* -------------------------------------------------------------------------- *)
(** Generic server library *)
(* -------------------------------------------------------------------------- *)

let request (ch :  ('a, 'b) chan_descr) (lk : Mutex.t) (req : 'a) : 'b =
  acquire lk;
  send ch req;
  let msg = recv ch in
  release lk;
  msg

let requests_handler_loop
    (request_handler : 'req * 'rep mcell -> unit)
    (ev_q :  ('req * 'rep mcell) mqueue) : unit  =
  let rec loop () : unit =
    (* Fetches the request and the reply cell from the queue. *)
    let req_ev = mqueue_fetch ev_q in
    (* Handles the request. *)
    request_handler req_ev;
    loop ()
  in loop ()

(** Serve requests on the the channel `c` via monitored queue of events. *)
let service_loop
    (c : ('rep, 'req) chan_descr)
    (mc : 'repl mcell)
    (ev_q : ('req * 'rep mcell) mqueue) : unit =
  let rec loop () =
    (* Receives the request. *)
    let req = recv c in
    (* Adds request together with reply cell to the queue & notifies the reqeust handler. *)
    mqueue_add ev_q (req, mc);
    (* Fetches the reply from the cell and sets the cell to None. *)
    let rep = mcell_fetch mc in
    (* Sends back the reply to the client *)
    send c rep;
    loop ()
  in loop ()

let accept_new_connections_loop
    (skt : ('repl, 'req) server_skt)
    (ev_q : ('req * 'rep mcell) mqueue) : unit =
  let rec loop () =
    (* Accept a connection from a new client. *)
    let new_conn = accept skt in
    let (chan, _addr) = new_conn in
    (* Create a monitored cell for replies to client requests. *)
    let cell = mcell_create () in
    (* Start serving the new client. *)
    fork (service_loop chan cell) ev_q;
    loop ()
  in loop ()

let run_server
    (ser[@metavar] : 'repl serializer)
    (deser[@metavar] : 'req serializer)
    (addr : saddr)
    (request_handler :  ('req * 'repl mcell) -> unit) : unit  =
  (* Create a server socket to accept incoming requests. *)
  let (skt :  ('repl, 'req) server_skt) = make_server_skt ser deser addr in
  server_listen skt;
  (* Create a monitored request event queue. *)
  let (evq :  ('req * 'repl mcell) mqueue) = mqueue_create () in
  (* Spawn a thread accepting connections and processing requests. *)
  fork (accept_new_connections_loop skt) evq;
  (* Spawn a thread handling incoming requests via the monitor event queue. *)
  fork (requests_handler_loop request_handler) evq

(* -------------------------------------------------------------------------- *)
(** Operations on log of requests *)
(* -------------------------------------------------------------------------- *)

(* TODO: The logs below should use by resizeable arrays instead of lists! *)
let log_create () : 'a log = ref (list_nil, 0) (* the log and next free index. *)
let log_add_entry (log : 'a log) (req : 'a wr_reqTy) =
  let lp = !log in
  let (data, next) = lp in
  let data' = list_append data (list_cons (req, next) list_nil) in
  log := (data', next + 1)
let log_next (log : 'a log) = snd !log
let log_length (log : 'a log) = snd !log
let log_get (log : 'a log) (i : int) : 'a option = list_nth (fst !log) i

(* -------------------------------------------------------------------------- *)
(** Monitored Log of write requests. *)
(* -------------------------------------------------------------------------- *)

let mlog_create () : 'a mlog =
  let mon = new_monitor () in
  let cell = log_create () in
  (mon, cell)

let mlog_add_entry (ml : 'a mlog) (req : 'a wr_reqTy) : unit =
  let (m, log) = ml in
  monitor_acquire m;
  log_add_entry log req;
  monitor_signal m;
  monitor_release m

let mlog_get_next (ml : 'a mlog) (i : int) : ('a wr_reqTy * int) =
  let (m, log) = ml in
  monitor_acquire m;
  (* Assumes 0 <= i <= |log|. *)
  let rec aux () =
    let n = log_next log in
    if n = i then
      begin
        monitor_wait m;
        aux () end
    else
      begin
        monitor_release m;
        unSOME (log_get log i)
      end
  in
  if i < 0 ||log_next log < i then assert false
  else aux ()

(* -------------------------------------------------------------------------- *)
(** Leader *)
(* -------------------------------------------------------------------------- *)

(** Processes the follower's request. *)
let follower_request_handler
    (mlog : 'a mlog) (req_ev : int * (('a wr_reqTy * int) mcell)) : unit =
  let (i, mc) = req_ev in
  let rep = mlog_get_next mlog i in
  mcell_set mc rep

(** Processes the request event (request & the reply cell). *)
let client_request_handler_at_leader
    (db : 'a dbTy Atomic.t) (log :'a mlog) (req_ev : 'a reqEvTy)  =
  let (req, mc) = req_ev in
  let (rep : 'a repTy) =
    (* Process the request. *)
    match req with
    | InjL p ->                  (* WRITE REQUEST *)
      let (k, v) = p in
      db := map_insert k v !db;  (* Write value v to the key k.  *)
      mlog_add_entry log (k,v);  (* Add the req to the monitored log and signal. *)
      InjL ()
    | InjR k ->                  (* READ REQUEST *)
      InjR (map_lookup k !db)    (* Read the key k. *)
  in
  mcell_set mc rep               (* Add the result to the associated reply cell. *)

(** Initialization of the leader-followers database. *)
let start_leader_processing_clients
    (ser[@metavar] : 'a serializer) (addr : saddr) (mlog : 'a mlog) =
  let (db : 'a dbTy Atomic.t) = ref (map_empty ()) in
  run_server (rep_l2c_ser ser) (req_c2l_ser ser) addr
    (client_request_handler_at_leader db mlog)

let start_leader_processing_followers
    (ser[@metavar] : 'a serializer) (addr : saddr) (log : 'a mlog) =
  run_server
    (rep_l2f_ser ser)
    req_f2l_ser addr
    (follower_request_handler log)

let init_leader (ser[@metavar] : 'a serializer) addr0 addr1 : unit =
  let mlog = mlog_create () in
  fork (start_leader_processing_clients ser addr0) mlog;
  fork (start_leader_processing_followers ser addr1) mlog

(* -------------------------------------------------------------------------- *)
(** Follower. *)
(* -------------------------------------------------------------------------- *)

(** Processes the read-only request event (request & the reply cell). *)
let client_request_handler_at_follower
    (db : 'a dbTy Atomic.t) (req_ev : 'a rd_reqEvTy) : unit =
  let (k, mc) = req_ev in
  let (rep : 'a option) = map_lookup k !db (* Read the key k. *)
  in mcell_set mc rep

let start_follower_processing_clients
    (ser[@metavar] : 'a serializer) (addr : saddr) (db : 'a dbTy Atomic.t) =
  run_server (rep_f2c_ser ser) req_c2f_ser addr
    (client_request_handler_at_follower db)

let sync_loop (ch :  (int, 'a log_entry) chan_descr)
    (db : 'a dbTy Atomic.t) (log : 'a log) : unit =
  let rec aux () =
    let i = log_next log in
    send ch i;
    let rep = recv ch in
    let ((k, v), j) = rep in
    assert (i = j);
    log_add_entry log (k,v) ;
    db := map_insert k v !db;
    aux ()
  in aux ()

let sync_with_server
    (ser[@metavar] : 'a serializer) (l_addr : saddr) (f2l_addr : saddr)
    (db : 'a dbTy Atomic.t) (log : 'a log) : unit =
  let skt = make_client_skt req_f2l_ser (rep_l2f_ser ser) f2l_addr in
  let ch = connect skt l_addr in
  sync_loop ch db log

(** Initialization of the follower. *)
let init_follower
    (ser[@metavar] : 'a serializer)
    (l_addr : saddr) (f2l_addr : saddr) (f_addr : saddr)  =
  let db = ref (map_empty ()) in
  let log = log_create () in
  sync_with_server ser l_addr f2l_addr db log;
  start_follower_processing_clients ser f_addr db

(* -------------------------------------------------------------------------- *)
(** Client Proxy Implementation. *)
(* -------------------------------------------------------------------------- *)

let init_client_leader_proxy (ser[@metavar]) clt_addr srv_addr =
  let skt = make_client_skt
      (req_c2l_ser ser)
      (rep_l2c_ser ser) clt_addr in
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

let init_client_follower_proxy (ser[@metavar]) clt_addr f_addr =
  let skt = make_client_skt req_c2f_ser (rep_f2c_ser ser) clt_addr in
  let ch = connect skt f_addr in
  let lk = newlock () in
  let read k  = request ch lk k in
  read


(* Generalization, with closures. *)
(*
let mcontainer_create
    (create : unit -> 't)
    (is_empty : 't -> bool)
    (update : 'elt -> 't -> 't)
    (fetch : 't -> 'elt * 't)
    (flag : bool) :
  (('elt -> unit) * (unit -> 'elt)) =
  let m = new_monitor () in
  let c = ref (create ()) in
  let rec mbox_wait_some () : 't =
    let rec aux () =
      let box = !c in
      if is_empty box then (monitor_wait m; aux ())
      else box
    in aux ()
  in
  let rec mbox_wait_none () : unit =
    let rec aux () =
      let box = !c in
      if not (is_empty box) then (monitor_wait m; aux ())
      else ()
    in aux ()
  in
  let mbox_update x : unit =
    monitor_acquire m;
    (if flag then mbox_wait_none () else ());
    c := update x !c;
    monitor_broadcast m;
    monitor_release m
  in
  let mbox_fetch () =
    monitor_acquire m;
    let box = mbox_wait_some () in
    let p = fetch box in
    let (elt, rem) = p in
    ignore (c := rem);
    monitor_release m;
    elt in
  (mbox_update, mbox_fetch)

let mcell_make () =
  let create () = None in
  let is_empty = fun c -> c = None in
  let update x _c = Some x in
  let fetch c =
    match c with
    | None -> assert false
    | Some v -> (v, None)
  in
  mcontainer_create create is_empty update fetch true

let mqueue_make () =
  let fetch q = unSOME (queue_take_opt q) in
  mcontainer_create queue_empty queue_is_empty queue_add fetch true
*)
