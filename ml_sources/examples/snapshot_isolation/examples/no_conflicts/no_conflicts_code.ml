open !Ast
open Serialization_code
open Network_util_code
open Snapshot_isolation_code
open Util_code

(** Example 1 *)
let example1_transaction_succeeds cst =
  start cst;
  write cst "x" 1;
  let b = commit cst in
  start cst;
  let rx = read cst "x" in
  if b then assert (rx = Some 1)
  else assert (rx = None);
  commitT cst

(** Example 2 *)
let writes_body cst =
  write cst "x" 37;
  write cst "y" 1

let writes_transaction_succeeds cst =
  start cst;
  writes_body cst;
  commitT cst

let writes_after_transaction_succeeds cst =
  start cst;
  wait_on_keyT cst (fun v -> v = 1) "y";
  let rx = unSOME (read cst "x") in
  assert (rx = 37);
  write cst "x" 40;
  commitT cst

(** read your writes *)
let writes_node caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  writes_transaction_succeeds cst

let write_after_node caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  writes_after_transaction_succeeds cst

let server srv =
  init_server int_serializer srv
