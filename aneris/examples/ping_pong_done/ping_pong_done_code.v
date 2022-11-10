(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/ping_pong/ping_pong_done_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib Require Import network_util_code.

Definition pong : val :=
  λ: "addr",
  let: "skt" := NewSocket in
  SocketBind "skt" "addr";;
  let: "msg" := unSOME (ReceiveFrom "skt") in
  let: "sender" := Snd "msg" in
  assert: ((Fst "msg") = #"PING");;
  SendTo "skt" #"PONG" "sender";;
  #();;
  letrec: "loop" <> :=
    let: "ack" := unSOME (ReceiveFrom "skt") in
    let: "body" := Fst "ack" in
    (if: "body" = #"PING"
     then  "loop" #()
     else  "body") in
    "loop" #().

Definition ping : val :=
  λ: "addr" "server",
  let: "skt" := NewSocket in
  SocketBind "skt" "addr";;
  SendTo "skt" #"PING" "server";;
  #();;
  let: "msg" := unSOME (ReceiveFrom "skt") in
  assert: ((Fst "msg") = #"PONG");;
  SendTo "skt" #"DONE" "server";;
  #().
