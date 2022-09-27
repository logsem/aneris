From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.examples.ping_pong Require Import ping_pong_done_code.

Definition ping_pong_runner : expr :=
  let: "pongaddr" := MakeAddress #"0.0.0.0" #80 in
  let: "pingaddr" := MakeAddress #"0.0.0.1" #80 in
  Start "0.0.0.0" (pong "pongaddr") ;;
  Start "0.0.0.1" (ping "pingaddr" "pongaddr").
