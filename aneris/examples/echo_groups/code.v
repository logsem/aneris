From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Export network_util_code.

Definition server1 : val :=
  λ: "addr",
  let: "socket" := NewSocket in
  SocketBind "socket" "addr";;
  "socket".

Definition server2 : val :=
  λ: "socket",
  let: "m" := unSOME (ReceiveFrom "socket") in "m".

Definition server3 : val :=
  λ: "socket" "m",
  let: "msg" := Fst "m" in
  let: "sender" := Snd "m" in
  SendTo "socket" #"done" "sender".

Definition server : val :=
  λ: "addr",
  let: "socket" := server1 "addr" in
  let: "m" := server2 "socket" in
  server3 "socket" "m".

Definition client : val := λ: "c_addr" "s_addr_1" "s_addr_2",
  let: "socket" := NewSocket in
  SocketBind "socket" "c_addr";;
  SendTo "socket" #"do" "s_addr_1";;
  SendTo "socket" #"do" "s_addr_2";;
  Fst (unSOME (ReceiveFrom "socket")).

Definition echo_runner : expr :=
  let: "c_addr" := MakeAddress #"0.0.0.0" #80 in
  let: "s_addr1" := MakeAddress #"0.0.0.1" #80 in
  let: "s_addr2" := MakeAddress #"0.0.0.2" #80 in
  Start "0.0.0.0" (client "c_addr" "s_addr1" "s_addr2") ;;
  Start "0.0.0.1" (server "s_addr1");;
  Start "0.0.0.2" (server "s_addr2").
