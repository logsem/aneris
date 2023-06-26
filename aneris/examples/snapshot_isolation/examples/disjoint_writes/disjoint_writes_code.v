From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.examples.snapshot_isolation Require Import snapshot_isolation_code.
From aneris.examples.snapshot_isolation.util Require Import util_code.

(* TODO : IMPLEMENT THOSE IN OCAML AND TRANSLATE TO COQ *)

Definition server : val := 
  λ: "addr",
  init_server int_serializer "addr".

Definition client_1 : val :=
  λ: "addr" "serveraddr",
  let: "rpc" := init_client_proxy int_serializer "addr" "serveraddr" in
  start "rpc" ;;
  write "rpc" #"x" #1 ;;
  commitT "rpc".

Definition client_2 : val :=
  λ: "addr" "serveraddr",
  let: "rpc" := init_client_proxy int_serializer "addr" "serveraddr" in
  start "rpc" ;;
  write "rpc" #"y" #1 ;;
  commitT "rpc".
