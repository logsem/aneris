open Ast
open Map_code
open Serialization_code
open Mt_server_code
open List_code

(** Serializers *)

let write_serializer (key_ser[@metavar]) (val_ser[@metavar]) =
  prod_serializer key_ser val_ser
let read_serializer (key_ser[@metavar]) = key_ser
let req_ser (key_ser[@metavar]) (val_ser[@metavar]) =
  (sum_serializer (write_serializer key_ser val_ser) (read_serializer key_ser))
let rep_ser (val_ser[@metavar]) =
  (sum_serializer (unit_serializer) (option_serializer val_ser))

let client_request_handler_at_server data hash req =
  let k = (* Get the request's key k *)
    match req with
    | InjL p ->
       fst p
    | InjR k ->
       k
  in
  let i = hash k in
  let p =
    match list_nth data i with
    | Some p -> p
    | None -> assert false
  in
  let (rpc, lk) = p in (* Get the data corresponding to the shard assigned to k *)
  acquire lk;
  let res = make_request rpc req in
  release lk;
  res

let start_server (key_ser[@metavar]) (val_ser[@metavar]) addr data hash () =
  run_server (rep_ser val_ser) (req_ser key_ser val_ser) addr
    (fun req -> client_request_handler_at_server data hash req)

let server_request_handler_at_shard db lk req =
  acquire lk;
  let res =
    match req with
    | InjL p ->                  (* WRITE REQUEST *)
       let (k, v) = p in
       db := map_insert k v !db;  (* Write value v to the key k.  *)
       InjL ()
    | InjR k ->                  (* READ REQUEST *)
       InjR (map_lookup k !db)    (* Read the key k. *)
  in
  release lk;
  res

let start_shard (key_ser[@metavar]) (val_ser[@metavar]) addr db lk () =
  run_server (rep_ser val_ser) (req_ser key_ser val_ser) addr
    (fun req -> server_request_handler_at_shard db lk req)

let init_server (key_ser[@metavar]) (val_ser[@metavar]) srv_addr addrs (hash : string -> int) =
  let data = list_map (
                 fun p ->
                 let (srv, shard) = p in
                 let rpc = init_client_proxy (req_ser key_ser val_ser) (rep_ser val_ser) srv shard in
                 let lk = newlock () in
                 (rpc, lk)) addrs in
  fork (start_server key_ser val_ser srv_addr data hash) ()

let init_shard (key_ser[@metavar]) (val_ser[@metavar]) addr =
  let db = ref (map_empty ()) in
  let lk = newlock () in
  fork (start_shard key_ser val_ser addr db lk) ()

let init_client (key_ser[@metavar]) (val_ser[@metavar]) clt_addr srv_addr =
  let rpc = init_client_proxy (req_ser key_ser val_ser) (rep_ser val_ser) clt_addr srv_addr in
  let lk = newlock () in
  let request req =
    acquire lk;
    let res = make_request rpc req in
    release lk;
    res
  in
  let write k w =
    match request (InjL (k, w)) with
    | InjL _u -> ()
    | InjR _abs -> assert false
  in
  let read k =
    match request (InjR k) with
    | InjL _abs -> assert false
    | InjR v -> v
  in
  (write, read)
