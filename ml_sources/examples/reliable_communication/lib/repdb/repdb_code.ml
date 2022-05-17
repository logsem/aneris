open Ast
open Map_code
open Network_util_code
open Serialization_code
open Log_code
open Client_server_code

(* Type definitions *)
type 'a wr_reqTy = string * 'a
type 'a reqTy = ('a wr_reqTy, string) sumTy
type 'a repTy = (unit, 'a option) sumTy
type 'a db_chan = ('a repTy, 'a reqTy) chan_descr
type 'a dbTy = ((string, 'a) amap)

(* -------------------------------------------------------------------------- *)
(** Serializers *)
(* -------------------------------------------------------------------------- *)
let write_serializer (val_ser[@metavar]) =
  prod_serializer string_serializer val_ser
let read_serializer = string_serializer
let req_c2l_ser (val_ser[@metavar]) =
  (sum_serializer (write_serializer val_ser) read_serializer)
let rep_l2c_ser (val_ser[@metavar]) =
  (sum_serializer (unit_serializer) (option_serializer val_ser))
let req_f2l_ser = int_serializer
let rep_l2f_ser (val_ser[@metavar]) =
  prod_serializer (prod_serializer string_serializer val_ser) int_serializer
let req_c2f_ser = read_serializer
let rep_f2c_ser (val_ser[@metavar]) =  option_serializer val_ser

(* -------------------------------------------------------------------------- *)
(** Generic methods for multi-threaded server with monitored requests. *)
(* -------------------------------------------------------------------------- *)

(** Serve requests on the the channel `c` via monitored queue of events. *)
let service_loop c mon (request_handler : monitor -> 'req -> 'rep) () : unit =
  let rec loop () =
    let req = recv c in
    monitor_acquire mon;
    let rep = request_handler mon req in
    monitor_release mon;
    send c rep;
    loop ()
  in loop ()

let accept_new_connections_loop skt mon request_handler () : unit =
  let rec loop () =
    let new_conn = accept skt in
    let (c, _a) = new_conn in
    fork (service_loop c mon request_handler) ();
    loop ()
  in loop ()

let run_server (ser[@metavar]) (deser[@metavar]) addr mon
    (request_handler : monitor -> 'req -> 'rep) : unit  =
  let (skt :  ('repl, 'req) server_skt) = make_server_skt ser deser addr in
  server_listen skt;
  fork (accept_new_connections_loop skt mon request_handler) ()

(* -------------------------------------------------------------------------- *)
(** Leader *)
(* -------------------------------------------------------------------------- *)

(** Processes the follower's request. *)
let follower_request_handler log mon req : 'a wr_reqTy log_entry =
  log_wait_until log mon req;
  unSOME (log_get log req)

(** Processes the request event (request & the reply cell). *)
let client_request_handler_at_leader
    (db : 'a dbTy Atomic.t) (log :'a log) (mon : monitor) (req : 'a reqTy) =
    match req with
    | InjL p ->                  (* WRITE REQUEST *)
      let (k, v) = p in
      db := map_insert k v !db;  (* Write value v to the key k.  *)
      log_add_entry log (k,v);
      monitor_signal mon;
      InjL ()
    | InjR k ->                  (* READ REQUEST *)
      InjR (map_lookup k !db)    (* Read the key k. *)

let update_log_copy_loop logC monC logF monF () =
  let rec loop i =
    monitor_acquire monC;     (* Phase 1: wait for the principal log changes. *)
    log_wait_until logC monC i;
    let logC_copy = !logC in
    monitor_release monC;
    monitor_acquire monF;     (* Phase 2: copy the log into read-only log. *)
    logF := logC_copy;
    monitor_broadcast monF;
    monitor_release monF;
    unsafe (fun () -> Unix.sleepf 3.0);
    loop (snd logC_copy)
  in loop 0

(** Initialization of the leader-followers database. *)
let start_leader_processing_clients (ser[@metavar]) addr db log mon () =
  run_server (rep_l2c_ser ser) (req_c2l_ser ser) addr mon
    (client_request_handler_at_leader db log)

let start_leader_processing_followers (ser[@metavar]) addr log mon () =
  run_server (rep_l2f_ser ser) req_f2l_ser addr mon
    (follower_request_handler log)

let init_leader (ser[@metavar]) addr0 addr1 : unit =
  let logC = log_create () in
  let logF = log_create () in
  let (db : 'a dbTy Atomic.t) = ref (map_empty ()) in
  let monC = new_monitor () in
  let monF = new_monitor () in
  fork (start_leader_processing_clients ser addr0 db logC monC) ();
  fork (start_leader_processing_followers ser addr1 logF monF) ();
  fork (update_log_copy_loop logC monC logF monF) ()

(* -------------------------------------------------------------------------- *)
(** Follower. *)
(* -------------------------------------------------------------------------- *)

(** Processes the read-only request event (request & the reply cell). *)
let client_request_handler_at_follower (db : 'a dbTy Atomic.t) _mon req_k  =
  map_lookup req_k !db (* Read the key k. *)

let start_follower_processing_clients (ser[@metavar]) addr db mon =
  run_server (rep_f2c_ser ser) req_c2f_ser addr mon
    (client_request_handler_at_follower db)

let sync_loop ch db log mon : unit =
  let rec aux () =
    let i = log_next log in
    send ch i;
    let rep = recv ch in
    let ((k, v), j) = rep in
    assert (i = j);
    monitor_acquire mon;
    log_add_entry log (k,v);
    db := map_insert k v !db;
    monitor_release mon;
    aux ()
  in aux ()

let sync_with_server (ser[@metavar]) l_addr f2l_addr db log mon : unit =
  let skt = make_client_skt req_f2l_ser (rep_l2f_ser ser) f2l_addr in
  let ch = connect skt l_addr in
  sync_loop ch db log mon

(** Initialization of the follower. *)
let init_follower (ser[@metavar]) l_addr f2l_addr f_addr  =
  let db = ref (map_empty ()) in
  let log = log_create () in
  let mon = new_monitor () in
  sync_with_server ser l_addr f2l_addr db log mon;
  start_follower_processing_clients ser f_addr db mon

(* -------------------------------------------------------------------------- *)
(** Client Proxies. *)
(* -------------------------------------------------------------------------- *)

let request (ch :  ('a, 'b) chan_descr) (lk : Mutex.t) (req : 'a) : 'b =
  acquire lk;
  send ch req;
  let msg = recv ch in
  release lk;
  msg

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
