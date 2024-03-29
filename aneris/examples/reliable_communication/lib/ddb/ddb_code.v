(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/reliable_communication/lib/ddb/ddb_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib Require Import queue_code.
From aneris.aneris_lang.lib Require Import map_code.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.examples.reliable_communication Require Import client_server_code.
From aneris.examples.reliable_communication.lib.ddb Require Import ddb_serialization_code.

Definition process_request : val :=
  λ: "db" "lkOut" "qOut" "req_ev",
  let: "req" := Fst "req_ev" in
  let: "chan" := Snd "req_ev" in
  let: "res" := match: "req" with
    InjL "p" =>
    let: "k" := Fst "p" in
    let: "v" := Snd "p" in
    "db" <- (map_insert "k" "v" ! "db");;
    InjL #()
  | InjR "k" => InjR (map_lookup "k" ! "db")
  end in
  acquire "lkOut";;
  "qOut" <- (queue_add ("res", "chan") ! "qOut");;
  release "lkOut".

Definition fetch_from_queue : val :=
  λ: "lk" "q",
  acquire "lk";;
  let: "tmp" := ! "q" in
  (if: ~ (queue_is_empty "tmp")
   then
     let: "qu" := unSOME (queue_take_opt "tmp") in
     let: "hd" := Fst "qu" in
     let: "tl" := Snd "qu" in
     "q" <- "tl";;
     #();;
     release "lk";;
     SOME "hd"
   else  NONE).

Definition request_loop : val :=
  λ: "db" "lkIn" "lkOut" "qIn" "qOut",
  letrec: "loop" <> :=
    let: "req_opt" := fetch_from_queue "lkIn" "qIn" in
    match: "req_opt" with
      NONE =>
      #() (* unsafe (fun () -> Unix.sleepf 0.5); loop () *);;
      "loop" #()
    | SOME "req" => process_request "db" "lkOut" "qOut" "req";;
                    "loop" #()
    end in
    "loop" #().

Definition recv_from_chan_loop : val :=
  λ: "c" "lkIn" "qIn",
  letrec: "loop" <> :=
    let: "req" := recv "c" in
    acquire "lkIn";;
    "qIn" <- (queue_add ("req", "c") ! "qIn");;
    release "lkIn";;
    "loop" #() in
    "loop" #().

Definition send_loop : val :=
  λ: "lkOut" "qOut",
  letrec: "loop" <> :=
    let: "reply_opt" := fetch_from_queue "lkOut" "qOut" in
    match: "reply_opt" with
      NONE =>
      #() (* unsafe (fun () -> Unix.sleepf 0.5); loop () *);;
      "loop" #()
    | SOME "ev" =>
        let: "repl" := Fst "ev" in
        let: "ch" := Snd "ev" in
        Fork (send "ch" "repl");;
        "loop" #()
    end in
    "loop" #().

Definition accept_new_connections_loop : val :=
  λ: "skt" "lkIn" "qIn",
  letrec: "loop" <> :=
    let: "new_conn" := accept "skt" in
    let: "clt_chan" := Fst "new_conn" in
    let: "_clt_addr" := Snd "new_conn" in
    Fork (recv_from_chan_loop "clt_chan" "lkIn" "qIn");;
    "loop" #() in
    "loop" #().

Definition init_server val_ser : val :=
  λ: "srv_addr",
  let: "db" := ref (map_empty #()) in
  let: "skt" := make_server_skt (reply_serializer val_ser)
                (request_serializer val_ser) "srv_addr" in
  let: "qIn" := ref (queue_empty #()) in
  let: "qOut" := ref (queue_empty #()) in
  let: "lkIn" := newlock #() in
  let: "lkOut" := newlock #() in
  Fork (send_loop "lkOut" "qOut");;
  server_listen "skt";;
  Fork (accept_new_connections_loop "skt" "lkIn" "qIn");;
  Fork (request_loop "db" "lkIn" "lkOut" "qIn" "qOut").

Definition request : val :=
  λ: "ch" "lk" "req",
  acquire "lk";;
  send "ch" "req";;
  let: "msg" := recv "ch" in
  release "lk";;
  "msg".

Definition install_proxy val_ser : val :=
  λ: "clt_addr" "srv_addr",
  let: "skt" := make_client_skt (request_serializer val_ser)
                (reply_serializer val_ser) "clt_addr" in
  let: "ch" := connect "skt" "srv_addr" in
  let: "lk" := newlock #() in
  let: "write" := λ: "k" "v",
  match: request "ch" "lk" (InjL ("k", "v")) with
    InjL "_u" => #()
  | InjR "_abs" => assert: #false
  end in
  let: "read" := λ: "k",
  match: request "ch" "lk" (InjR "k") with
    InjL "_abs" => assert: #false
  | InjR "r" => "r"
  end in
  ("write", "read").
