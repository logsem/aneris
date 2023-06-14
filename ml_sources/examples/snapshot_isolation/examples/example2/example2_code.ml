open !Ast
open Serialization_code
open Snapshot_isolation_code
open Util_code

let transaction1 cst =
  start cst;
  write cst "x" 1;
  write cst "y" 1;
  commitT cst

(* Transactions are isolated : even though x was written first, the changes on x and y are seen in the same time. *)
let transaction2 cst =
  start cst;
  wait_on_keyT cst (fun v -> v = 1) "x";
  let vy = read cst "y" in
  commitT cst;
  assert (vy = Some 1)

let transaction1_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction1 cst

let transaction2_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction2 cst

let server srv =
  init_server int_serializer srv
