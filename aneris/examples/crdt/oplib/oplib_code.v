(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/crdt/oplib/oplib_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib Require Import list_code.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_code.
From aneris.examples.rcb Require Import rcb_code.

Definition get_state : val :=
  λ: "lock" "st" <>,
  acquire "lock";;
  let: "res" := ! "st" in
  release "lock";;
  "res".

Definition apply_thread : val :=
  λ: "lock" "deliver" "st" "effect",
  loop_forever (λ: <>,
                acquire "lock";;
                match: "deliver" #() with
                  SOME "msg" => "st" <- ("effect" "msg" ! "st")
                | NONE => #()
                end;;
                release "lock").

Definition update : val :=
  λ: "lock" "broadcast" "st" "effect" "op",
  acquire "lock";;
  let: "msg" := "broadcast" "op" in
  "st" <- ("effect" "msg" ! "st");;
  release "lock".

Definition oplib_init op_ser op_deser : val :=
  λ: "addrs" "rid" "crdt",
  let: "rcbInitRes" := rcb_init op_ser op_deser "addrs" "rid" in
  let: "deliver" := Fst "rcbInitRes" in
  let: "broadcast" := Snd "rcbInitRes" in
  let: "crdt_res" := "crdt" #() in
  let: "init_st" := Fst "crdt_res" in
  let: "effect" := Snd "crdt_res" in
  let: "st" := ref ("init_st" #()) in
  let: "lock" := newlock #() in
  Fork (apply_thread "lock" "deliver" "st" "effect");;
  (get_state "lock" "st", update "lock" "broadcast" "st" "effect").
