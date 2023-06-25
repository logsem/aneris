open !Ast
open Serialization_code
open Snapshot_isolation_code
open Util_code

(* Transactions that write to different keys can commit simultaneously *)

let transaction1 cst =
  start cst;
  write cst "x" 1;
  commitT cst

let transaction2 cst =
  start cst;
  write "y" 1;
  commitT cst

let transaction1_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction1 cst

let transaction2_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction2 cst

let server srv =
  init_server int_serializer srv
