(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/transactional_consistency/read_committed/examples/commit_order/commit_order_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.examples.transactional_consistency.snapshot_isolation Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency.snapshot_isolation.util Require Import util_code.

Definition transaction1 : val :=
  λ: "cst",
  start "cst";;
  write "cst" #"x" #1;;
  let: "vy" := read "cst" #"y" in
  (if: "vy" = (SOME #1)
   then  write "cst" #"a" #1
   else  #());;
  commitU "cst".

Definition transaction2 : val :=
  λ: "cst",
  start "cst";;
  write "cst" #"y" #1;;
  let: "vx" := read "cst" #"x" in
  (if: "vx" = (SOME #1)
   then  write "cst" #"b" #1
   else  #());;
  commitU "cst".

Definition transaction3 : val :=
  λ: "cst",
  start "cst";;
  let: "va" := read "cst" #"a" in
  let: "vb" := read "cst" #"b" in
  assert: (~ (("va" = (SOME #1)) && ("vb" = (SOME #1))));;
  commitU "cst".

Definition transaction1_client : val :=
  λ: "caddr" "kvs_addr",
  let: "cst" := init_client_proxy int_serializer "caddr" "kvs_addr" in
  transaction1 "cst".

Definition transaction2_client : val :=
  λ: "caddr" "kvs_addr",
  let: "cst" := init_client_proxy int_serializer "caddr" "kvs_addr" in
  transaction2 "cst".

Definition transaction3_client : val :=
  λ: "caddr" "kvs_addr",
  let: "cst" := init_client_proxy int_serializer "caddr" "kvs_addr" in
  transaction3 "cst".

Definition server : val := λ: "srv", init_server int_serializer "srv".