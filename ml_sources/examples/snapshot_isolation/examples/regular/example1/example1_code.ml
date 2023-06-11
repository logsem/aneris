open !Ast
open Serialization_code
open Snapshot_isolation_code
open Util_code

let example11_transaction cst =
  start cst;
  write cst "x" 1;
  let b = commit cst in
  start cst;
  let rx = read cst "x" in
  if b then assert (rx = Some 1)
  else assert (rx = None);
  commitU cst

(** read your writes *)
let example11_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  example11_transaction cst

let example12_transaction cst =
  start cst;
  write cst "x" 1;
  let b1 = commit cst in
  start cst;
  write cst "x" 2;
  let b2 = commit cst in
  start cst;
  let rx = read cst "x" in
  if b1 && b2 then assert (rx = Some 2)
  else ();
  commitU cst

(** writes follow writes *)
let example12_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  example12_transaction cst

let server srv =
  init_server int_serializer srv
