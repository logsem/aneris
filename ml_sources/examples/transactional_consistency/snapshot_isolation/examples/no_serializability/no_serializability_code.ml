open !Ast
open Serialization_code
open Network_util_code
open Snapshot_isolation_code
open Util_code

let transaction1 cst =
  start cst;
  write cst "x" 1;
  write cst "y" 1;
  write cst "z" 1;
  commitU cst

let transaction2 cst =
  wait_transaction cst (fun v -> v = 1) "z";
  start cst;
  let vx = read cst "x" in
  if vx = Some 1 then
    write cst "y" (-1);
  commitU cst

let transaction3 cst =
  wait_transaction cst (fun v -> v = 1) "z";
  start cst;
  let vy = read cst "y" in
  if vy = Some 1 then
    write cst "x" (-1);
  commitU cst

let transaction4 cst =
  wait_transaction cst (fun v -> v = 1) "z";
  start cst;
  let vx = unSOME (read cst "x") in
  let vy = unSOME (read cst "y") in
  let r = vx + vy in
  (* The case r = -2 would not happen in case of serializability *)
  assert (r = -2 || 0 <= r);
  commitU cst

let transaction1_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction1 cst

let transaction2_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction2 cst

let transaction3_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction3 cst

let transaction4_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction4 cst

let server srv =
  init_server int_serializer srv
