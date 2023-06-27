(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/snapshot_isolation/examples/no_conflicts/no_conflicts_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.examples.snapshot_isolation Require Import snapshot_isolation_code.
From aneris.examples.snapshot_isolation.util Require Import util_code.

Definition example1_transaction_succeeds : val :=
  λ: "cst",
  start "cst";;
  write "cst" #"x" #1;;
  let: "b" := commit "cst" in
  start "cst";;
  let: "rx" := read "cst" #"x" in
  (if: "b"
   then  assert: ("rx" = (SOME #1))
   else  assert: ("rx" = NONE));;
  commitT "cst".

Definition writes_body : val :=
  λ: "cst", write "cst" #"x" #37;;
             write "cst" #"y" #1.

Definition writes_transaction_succeeds : val :=
  λ: "cst", start "cst";;
             writes_body "cst";;
             commitT "cst".

Definition writes_after_transaction_succeeds : val :=
  λ: "cst",
  start "cst";;
  wait_on_keyT "cst" (λ: "v", "v" = #1) #"y";;
  let: "rx" := unSOME (read "cst" #"x") in
  assert: ("rx" = #37);;
  write "cst" #"x" #40;;
  commitT "cst".

Definition writes_node : val :=
  λ: "caddr" "kvs_addr",
  let: "cst" := init_client_proxy int_serializer "caddr" "kvs_addr" in
  writes_transaction_succeeds "cst".

Definition write_after_node : val :=
  λ: "caddr" "kvs_addr",
  let: "cst" := init_client_proxy int_serializer "caddr" "kvs_addr" in
  writes_after_transaction_succeeds "cst".

Definition server : val := λ: "srv", init_server int_serializer "srv".