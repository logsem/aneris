From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.examples.snapshot_isolation Require Import snapshot_isolation_code.
From aneris.examples.snapshot_isolation.util.util_deprecated Require Import util_code.

(* TODO : IMPLEMENT THOSE IN OCAML AND TRANSLATE TO COQ *)

Definition server : val := 
  λ: "addr",
  init_server int_serializer "addr".

Definition transaction : val :=
  λ: "addr" "serveraddr" "value",
  let: "rpc" := init_client_proxy int_serializer "addr" "serveraddr" in
  start "rpc" ;;
  write "rpc" #"x" "value" ;;
  write "rpc" #"y" "value" ;;
  commit "rpc".

Definition client_1 : val :=
  λ: "addr" "serveraddr",
  transaction "addr" "serveraddr" #1.

Definition client_2 : val :=
  λ: "addr" "serveraddr",
  transaction "addr" "serveraddr" #2.

Definition client_3 : val :=
  λ: "addr" "serveraddr",
  let: "rpc" := init_client_proxy int_serializer "addr" "serveraddr" in
  start "rpc" ;;
  let: "vx" := read "rpc" #"x"  in
  let: "vy" := read "rpc" #"y" in
  commitT "rpc" ;;
  assert: ("vx" = "vy").