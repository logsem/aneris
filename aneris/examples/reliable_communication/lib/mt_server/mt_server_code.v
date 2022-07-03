(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/reliable_communication/lib/mt_server/mt_server_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.examples.reliable_communication Require Import client_server_code.

Definition service_loop : val :=
  λ: "c" "request_handler" <>,
  letrec: "loop" <> :=
    let: "req" := recv "c" in
    let: "rep" := "request_handler" "req" in
    send "c" "rep";;
    "loop" #() in
    "loop" #().

Definition accept_new_connections_loop : val :=
  λ: "skt" "request_handler" <>,
  letrec: "loop" <> :=
    let: "new_conn" := accept "skt" in
    let: "c" := Fst "new_conn" in
    let: "_a" := Snd "new_conn" in
    Fork (service_loop "c" "request_handler" #());;
    "loop" #() in
    "loop" #().

Definition run_server ser deser : val :=
  λ: "addr" "request_handler",
  let: "skt" := make_server_skt ser deser "addr" in
  server_listen "skt";;
  Fork (accept_new_connections_loop "skt" "request_handler" #()).

Definition make_request : val := λ: "ch" "req", send "ch" "req";;
                                                 recv "ch".

Definition init_client_proxy ser deser : val :=
  λ: "clt_addr" "srv_addr",
  let: "skt" := make_client_skt ser deser "clt_addr" in
  let: "ch" := connect "skt" "srv_addr" in
  "ch".
