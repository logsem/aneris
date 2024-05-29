From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.examples.transactional_consistency.snapshot_isolation Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency Require Import wrapped_library.
From aneris.examples.transactional_consistency.snapshot_isolation.util Require Import util_code.

Definition transaction1 : val :=
  λ: "cst", (wrap_start start) "cst";;
             (wrap_write write) "cst" #"x" #1;;
             loop #().

Definition transaction2 : val :=
  λ: "cst",
  (wrap_start start) "cst";;
  let: "vx" := (wrap_read read) "cst" #"x" in
  assert: ("vx" = NONE);;
  (wrap_commit commit) "cst" ;;
  #().

Definition transaction1_client : val :=
  λ: "caddr" "kvs_addr",
  let: "cst" := init_client_proxy int_serializer "caddr" "kvs_addr" in
  transaction1 "cst".

Definition transaction2_client : val :=
  λ: "caddr" "kvs_addr",
  let: "cst" := init_client_proxy int_serializer "caddr" "kvs_addr" in
  transaction2 "cst".

Definition server : val := λ: "srv", init_server int_serializer "srv".
