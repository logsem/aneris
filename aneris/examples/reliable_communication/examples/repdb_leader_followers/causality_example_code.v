(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/reliable_communication/examples/repdb_leader_followers/causality_example_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.examples.reliable_communication.lib.repdb Require Import repdb_code.

Definition do_writes : val := λ: "wr", "wr" #"x" #37;;
                                        "wr" #"y" #1.

Definition wait_on_read : val :=
  λ: "rd" "k" "v",
  letrec: "loop" <> :=
    let: "res" := "rd" "k" in
    (if: "res" = (SOME "v")
     then  #()
     else
       #() (* unsafe (fun () -> Unix.sleepf 2.0); loop ()) *);;
       "loop" #()) in
    "loop" #().

Definition do_reads : val :=
  λ: "rd",
  wait_on_read "rd" #"y" #1;;
  let: "vx" := "rd" #"x" in
  assert: ("vx" = (SOME #37)).

Definition node0 : val :=
  λ: "clt_addr0" "db_laddr",
  let: "db_funs" := init_client_leader_proxy int_serializer "clt_addr0"
                    "db_laddr" in
  let: "wr" := Fst "db_funs" in
  let: "_rd" := Snd "db_funs" in
  do_writes "wr".

Definition node1 : val :=
  λ: "clt_addr1" "faddr",
  let: "rd" := init_client_follower_proxy int_serializer "clt_addr1" "faddr" in
  do_reads "rd".
