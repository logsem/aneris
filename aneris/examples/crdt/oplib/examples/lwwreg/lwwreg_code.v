(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/crdt/oplib/examples/lwwreg/lwwreg_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_code.
From aneris.examples.crdt.oplib Require Import oplib_code.

Definition lwwreg_init_st : val := λ: <>, NONE.

Definition vc_to_lamport : val :=
  rec: "vc_to_lamport" "vc" :=
  match: "vc" with
    NONE => #0
  | SOME "p" =>
      let: "h" := Fst "p" in
      let: "t" := Snd "p" in
      "h" + ("vc_to_lamport" "t")
  end.

Definition vect_eq : val :=
  λ: "vc" "vc'", (vect_leq "vc" "vc'") && (vect_leq "vc'" "vc").

Definition vect_lt : val :=
  λ: "vc" "vc'", (vect_leq "vc" "vc'") && (~ (vect_eq "vc" "vc'")).

Definition tstamp_lt : val :=
  λ: "ts1" "ts2",
  let: "vc1" := Fst "ts1" in
  let: "o1" := Snd "ts1" in
  let: "ts1" := vc_to_lamport "vc1" in
  let: "vc2" := Fst "ts2" in
  let: "o2" := Snd "ts2" in
  let: "ts2" := vc_to_lamport "vc2" in
  ("ts1" < "ts2") || (("ts1" = "ts2") && ("o1" < "o2")).

Definition lwwreg_effect : val :=
  λ: "msg" "reg",
  match: "reg" with
    NONE => SOME "msg"
  | SOME "reg'" =>
      let: "_v" := Fst (Fst "reg'") in
      let: "curr_vc" := Snd (Fst "reg'") in
      let: "curr_orig" := Snd "reg'" in
      let: "curr_ts" := ("curr_vc", "curr_orig") in
      let: "_v'" := Fst (Fst "msg") in
      let: "new_vc" := Snd (Fst "msg") in
      let: "new_orig" := Snd "msg" in
      let: "new_ts" := ("new_vc", "new_orig") in
      (if: tstamp_lt "curr_ts" "new_ts"
       then  SOME "msg"
       else
         (if: tstamp_lt "new_ts" "curr_ts"
         then  "reg"
         else  assert: #false))
  end.

Definition lwwreg_crdt : val := λ: <>, (lwwreg_init_st, lwwreg_effect).

Definition lwwreg_init val_ser val_deser : val :=
  λ: "addrs" "rid",
  let: "initRes" := oplib_init val_ser val_deser "addrs" "rid" lwwreg_crdt in
  let: "get_state" := Fst "initRes" in
  let: "update" := Snd "initRes" in
  ("get_state", "update").
