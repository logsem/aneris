open !Ast
open Serialization_code
open Snapshot_isolation_code
open Util_code

let transaction cst f =
  start cst;
  let vx = read cst "x" in
  let r = f vx in
  write cst "x" r;
  commitU cst

let client caddr kvs_addr f =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction cst f

let server srv =
  init_server int_serializer srv
