open !Ast
open Serialization_code
open Network_util_code
open Snapshot_isolation_code
open Util_code

let writes_body cst =
  write cst "x" 37;
  write cst "y" 1

let writes_transaction cst =
  start cst;
  writes_body cst;
  commit cst

let reads_transaction cst =
  start cst;
  wait_on_key cst (fun v -> v = 1) "y";
  let rx = unSOME (read cst "x") in
  assert (rx = 37);
  commit cst

(** read your writes *)
let writes_node caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  writes_transaction cst

let node_read caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  reads_transaction cst

let server srv =
  init_server int_serializer srv
