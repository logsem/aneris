open Ast
open Map_code
open Network_util_code
open Serialization_code
open Log_code
open Mt_server_code

(* Type aliases *)
type 'a reqTy = (string * 'a, string) sumTy
type 'a repTy = (unit, 'a option) sumTy
type 'a dbTy = ((string, 'a) amap)

(** Serializers *)

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

(** Leader *)

(** Processes the follower's request. *)
let follower_request_handler log mon req : ((string * 'a) * int) =
  log_wait_until log mon req;
  unSOME (log_get log req)

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

let start_leader_processing_followers (ser[@metavar]) addr log mon () =
  run_server (rep_l2f_ser ser) req_f2l_ser addr mon
    (follower_request_handler log)

(** Processes the request event (request & the reply cell). *)
let client_request_handler_at_leader (db : 'a dbTy Atomic.t) (log :  ((string * 'a) * int) log)
    (mon : monitor) (req : 'a reqTy) : 'a repTy =
    match req with
    | InjL p ->                  (* WRITE REQUEST *)
      let (k, v) = p in
      db := map_insert k v !db;  (* Write value v to the key k.  *)
      let n = log_length log in
      log_add_entry log ((k,v), n);
      monitor_signal mon;
      InjL ()
    | InjR k ->                  (* READ REQUEST *)
      InjR (map_lookup k !db)    (* Read the key k. *)

(** Initialization of the leader-followers database. *)
let start_leader_processing_clients (ser[@metavar]) addr db log mon () =
  run_server (rep_l2c_ser ser) (req_c2l_ser ser) addr mon
    (client_request_handler_at_leader db log)

let init_leader (ser[@metavar] : 'a serializer) addr0 addr1 : unit =
  let logC = log_create () in
  let logF = log_create () in
  let (db : 'a dbTy Atomic.t) = ref (map_empty ()) in
  let monC = new_monitor () in
  let monF = new_monitor () in
  fork (start_leader_processing_clients ser addr0 db logC monC) ();
  fork (start_leader_processing_followers ser addr1 logF monF) ();
  fork (update_log_copy_loop logC monC logF monF) ()

let init_client_leader_proxy (ser[@metavar]) clt_addr srv_addr =
 let reqf = init_client_proxy (req_c2l_ser ser) (rep_l2c_ser ser) clt_addr srv_addr in
 let write k v =
    match reqf (InjL (k, v)) with
    | InjL _u -> ()
    | InjR _abs -> assert false in
  let read k  =
    match reqf (InjR k) with
    | InjL _abs -> assert false
    | InjR r -> r
  in (write, read)

(** Follower. *)

(** Processes the read-only request event (request & the reply cell). *)
let client_request_handler_at_follower (db : 'a dbTy Atomic.t) _mon req_k  =
  map_lookup req_k !db (* Read the key k. *)

let start_follower_processing_clients (ser[@metavar]) addr db mon =
  run_server (rep_f2c_ser ser) req_c2f_ser addr mon
    (client_request_handler_at_follower db)

let sync_loop db log mon reqf () : unit =
  let rec aux () =
    let i = log_next log in
    let rep = reqf i in
    let ((k, v), j) = rep in
    assert (i = j);
    monitor_acquire mon;
    log_add_entry log ((k,v), j);
    db := map_insert k v !db;
    monitor_release mon;
    aux ()
  in aux ()

let sync_with_server (ser[@metavar]) l_addr f2l_addr db log mon : unit =
  let reqf = init_client_proxy req_f2l_ser (rep_l2f_ser ser) f2l_addr l_addr in
  fork (sync_loop db log mon reqf) ()

(** Initialization of the follower. *)
let init_follower (ser[@metavar]) l_addr f2l_addr f_addr  =
  let db = ref (map_empty ()) in
  let log = log_create () in
  let mon = new_monitor () in
  sync_with_server ser l_addr f2l_addr db log mon;
  start_follower_processing_clients ser f_addr db mon

let init_client_follower_proxy (ser[@metavar]) clt_addr srv_addr =
  init_client_proxy req_c2f_ser (rep_f2c_ser ser) clt_addr srv_addr
