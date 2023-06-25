open !Ast
open Serialization_code
open Snapshot_isolation_code
open Util_code

let transaction1 cst =
  start cst;
  write cst "x" 1;
  commitU cst

(* Read-only transactions will always commit *)
let transaction2 cst =
  start cst;
  let _vx = read cst "x" in
  commitT cst

let transaction1_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction1 cst

let transaction2_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction2 cst

let server srv =
  init_server int_serializer srv
