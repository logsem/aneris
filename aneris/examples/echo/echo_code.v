From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Export network_util_code.

Definition echo_server : val :=
  λ: "addr",
    let: "socket" := NewSocket #PF_INET #SOCK_DGRAM #IPPROTO_UDP in
    SocketBind "socket" "addr";;
    (rec: "go" <> :=
        let: "m" := unSOME $ ReceiveFrom "socket" in
        let: "m1" := Fst "m" in
        let: "m2" := Snd "m" in
        SendTo "socket" "m1" "m2";;
        "go" #()) #().

Definition echo_client : val := λ: "c_addr" "s_addr",
  let: "socket" := NewSocket #PF_INET #SOCK_DGRAM #IPPROTO_UDP in
  SocketBind "socket" "c_addr";;
  SendTo "socket" #"Hello" "s_addr";;
  let: "m1" := unSOME (ReceiveFrom "socket") in
  SendTo "socket" #"World" "s_addr";;
  let: "m2" := unSOME (ReceiveFrom "socket") in
  if: "m1" ≠ "m2" then
    let: "m1'" := Fst "m1" in
    let: "m2'" := Fst "m2" in
    assert: ("m1'" = #"Hello");;
    assert: ("m2'" = #"World")
  else #().

Definition echo_runner : expr :=
  let: "s_addr" := MakeAddress #"0.0.0.0" #80 in
  let: "c_addr" := MakeAddress #"0.0.0.1" #80 in
  Start "0.0.0.0" (echo_server "s_addr");;
  Start "0.0.0.0" (echo_client "c_addr" "s_addr").
