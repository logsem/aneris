open Ast
open Map_code
open Serialization_code
open Mt_server_code

(** ************************************************************* *)
(** ********************* SERVER SIDE *************************** *)
(** ************************************************************* *)

(** The types of requests and replies *)

(** [[Write(k,v) | Read(k)] | [Start() | Commit()]] *)
type 'a reqTy = (((string * 'a, string) sumTy), (unit, unit) sumTy) sumTy

(** [Accept | AcceptRead(option v)]*)
type 'a repTy = (unit, 'a option) sumTy

(* Request Events. *)
let write k v : 'a reqTy = InjL (InjL (k, v))
let read k : 'a reqTy = InjL (InjR k)
let start () : 'a reqTy = InjR (InjL ())
let commit () : 'a reqTy = InjR (InjR ())

(** Reply Events. *)
let accept () : 'a repTy = InjL ()
let accept_read vo : 'a repTy = InjR vo

(** Serializers *)
let write_serializer (val_ser[@metavar]) = prod_serializer string_serializer val_ser
let read_serializer = string_serializer
let kvs_serializer (val_ser[@metavar]) = sum_serializer (write_serializer val_ser) read_serializer
let start_serializer = unit_serializer
let commit_serializer = unit_serializer
let lock_serializer = sum_serializer start_serializer commit_serializer
let req_c2l_ser (val_ser[@metavar]) = sum_serializer (kvs_serializer val_ser) lock_serializer

let accept_serializer = unit_serializer
let accept_read_serializer (val_ser[@metavar]) = option_serializer (val_ser)                                                             
let rep_l2c_ser (val_ser[@metavar]) = sum_serializer accept_serializer (accept_read_serializer val_ser)

(** The internal state of the server *)
type 'a dbTy = ((string, 'a) amap) Atomic.t
type lockTy = Mutex.t

(** Processes the request event. *)
let client_request_handler
    (lock : lockTy) (db : 'a dbTy)
    (reqo : 'a reqTy option) : 'a repTy option =
  let res =
    match reqo with
    (* TIMEOUT ON LISTENING *)
    | None -> None
    (* RECEIVING A NEW REQUEST *)
    | Some req ->
      match req with
      (* START OR COMMIT REQUEST *)
      | InjR lock_req ->
        (match lock_req with
        (* START REQUEST *)
        | InjL () -> 
          acquire lock;
          Some (accept ());
        (* COMMIT REQUEST *)
        | InjR () -> 
          release lock;
          Some (accept ()))
      (* WRITE OR READ REQUEST *)
      | InjL db_req ->
        match db_req with
        (* WRITE REQUEST *)
        | InjL (k, v) ->
          db := map_insert k v !db;
          Some (accept ())
        (* READ REQUEST *)
        | InjR k ->
          let vo = map_lookup k !db in
          Some (accept_read vo)
  in res

(** Initialization of the database. *)
let start_server_processing_clients (ser[@metavar]) addr lock db () =
  run_server_opt (rep_l2c_ser ser) (req_c2l_ser ser) addr
    (fun req -> client_request_handler lock db req)

let init_server (ser[@metavar] : 'a serializer) addr () : unit =
  let (db : 'a dbTy) = ref (map_empty ()) in
  let (lock : lockTy) = newlock () in
  fork (start_server_processing_clients ser addr lock db) ()

(** ************************************************************* *)
(** ********************* CLIENT SIDE *************************** *)
(** ************************************************************* *)

(* Function for initializing client connections. Each client can intialize multiple 
   connections but can only execute one transactions at a time on a single connection *)
let init_client_proxy (ser[@metavar]) clt_addr srv_addr =
  let rpc = init_client_proxy (req_c2l_ser ser) (rep_l2c_ser ser) clt_addr srv_addr in
  let active = ref false in (* Boolean keeping track of wheter a transaction has been started *)
  let lock = newlock () in (* Lock for serializing concurrent client envocations *)
  let start () : unit =
    acquire lock;
    if !active then (
      assert false
    ) else (
      match make_request rpc (start ()) with
      (* ACCEPT *)
      | InjL () -> 
        active := true; 
        release lock;
        ()
      (* ACCEPT_READ *)
      | InjR _ -> assert false
    )
  in
  let commit () : unit option =
    acquire lock;
    if !active then (
      match make_request rpc (commit ()) with
      (* ACCEPT *)
      | InjL () -> 
        active := false;
        release lock;
        Some ()
      (* ACCEPT_READ *)
      | InjR _ -> assert false
    ) else (
        assert false
    )
  in
  let write k v : unit option =
    acquire lock;
    if !active then (
      match make_request rpc (write k v) with
      (* ACCEPT *)
      | InjL () -> 
        release lock;
        Some ()
      (* ACCEPT_READ *)
      | InjR _ -> assert false
    ) else (
      assert false
    )
  in
  let read k : 'a option =
    acquire lock;
    if !active then (
      match make_request rpc (read k) with
      (* ACCEPT *)
      | InjL () -> assert false
      (* ACCEPT_READ *)
      | InjR vo -> 
        release lock;
        vo
    ) else (
      assert false
    )
  in ((start, commit), (write, read))