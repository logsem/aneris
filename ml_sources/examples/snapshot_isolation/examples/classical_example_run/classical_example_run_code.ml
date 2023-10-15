open !Ast
open Serialization_code
open Snapshot_isolation_code
open Util_code

let transaction1 cst =
  write cst "x" 1;
  write cst "y" 1

let transaction2 cst =
  write cst "x" 2;
  write cst "y" 2

let transaction3 cst =
  let vx = read cst "x" in
  let vy = read cst "y" in
  assert(vx = vy)

let transaction1_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  run cst transaction1

let transaction2_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  run cst transaction2

let transaction3_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  run cst transaction3

let server srv =
  init_server int_serializer srv