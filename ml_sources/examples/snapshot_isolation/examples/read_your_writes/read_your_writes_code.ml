open !Ast
open Serialization_code
open Snapshot_isolation_code
open Util_code

let transaction cst =
  start cst;
  write cst "x" 1;
  let vx = read cst "x" in
  assert (vx = Some 1);
  commitU cst

let transaction_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction cst

let server srv =
  init_server int_serializer srv
