From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib Require Export network_util_code.

Definition pong : val :=
  λ: "addr",
  let: "socket" := NewSocket #PF_INET #SOCK_DGRAM #IPPROTO_UDP in
  SocketBind "socket" "addr";;
  let: "m" := unSOME (ReceiveFrom "socket") in
  let: "msg" := Fst "m" in
  let: "sender" := Snd "m" in
  (if: "msg" = #"PING" then SendTo "socket" #"PONG" "sender"
   else assert #false).

Definition ping : val :=
  λ: "addr" "server",
  let: "socket" := NewSocket #PF_INET #SOCK_DGRAM #IPPROTO_UDP in
  SocketBind "socket" "addr";;
  SendTo "socket" #"PING" "server";;
  Fst (unSOME (ReceiveFrom "socket")).

Definition ping_pong_runner : expr :=
  let: "pongaddr" := MakeAddress #"0.0.0.0" #80 in
  let: "pingaddr" := MakeAddress #"0.0.0.1" #80 in
  Start "0.0.0.0" (pong "pongaddr") ;;
  Start "0.0.0.1" (ping "pingaddr" "pongaddr").
