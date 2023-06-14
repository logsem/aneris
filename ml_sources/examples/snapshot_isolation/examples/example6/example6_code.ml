open !Ast
open Serialization_code
open Snapshot_isolation_code
open Util_code

let transaction1 cst f =
  start cst;
  wait_on_keyT cst (fun v -> v = 0) "x";
  let vy = match read cst "y" with Some v -> v | None -> assert false in
  let ret = f vy in
  write cst "y" ret;
  write cst "x" 1;
  commitT cst

let transaction2 cst f =
  start cst;
  write cst "x" 0;
  write cst "y" 42;
  wait_on_keyT cst (fun v -> v = 1) "x";
  let ret = read cst "y" in
  commitT cst;
  assert (ret = Some (f 42))

let transaction1_client caddr kvs_addr f =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction1 cst f

let transaction2_client caddr kvs_addr f =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction2 cst f

let server srv =
  init_server int_serializer srv
