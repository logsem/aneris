(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/crdt/statelib/examples/pncounter/counter_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.aneris_lang.lib Require Import list_code.
From aneris.examples.crdt.statelib Require Import statelib_code.

Definition mutate_side : val :=
  λ: "updl" "keepl" "i" "op",
  let: "v" := unSOME (list_nth "updl" "i") in
  (list_update "updl" "i" ("v" + "op"), "keepl").

Definition mutator : val :=
  λ: "i" "cpt" "op",
  let: "posl" := Fst "cpt" in
  let: "negl" := Snd "cpt" in
  (if: #0 ≤ "op"
   then  mutate_side "posl" "negl" "i" "op"
   else  mutate_side "negl" "posl" "i" (- "op")).

Definition merge_aux : val :=
  λ: "l1" "l2",
  letrec: "aux" "l" "r" :=
    match: "l" with
      NONE => match: "r" with
        NONE => NONE
      | SOME "_p" => assert: #false
      end
    | SOME "sl" =>
        match: "r" with
          NONE => assert: #false
        | SOME "sr" =>
            let: "x" := Fst "sl" in
            let: "slt" := Snd "sl" in
            let: "y" := Fst "sr" in
            let: "srt" := Snd "sr" in
            let: "rs" := (if: "x" ≤ "y"
             then  "y"
             else  "x") in
            let: "tl" := "aux" "slt" "srt" in
            "rs" :: "tl"
        end
    end in
    "aux" "l1" "l2".

Definition merge : val :=
  λ: "st1" "st2",
  let: "pl1" := Fst "st1" in
  let: "nl1" := Snd "st1" in
  let: "pl2" := Fst "st2" in
  let: "nl2" := Snd "st2" in
  let: "pres" := merge_aux "pl1" "pl2" in
  let: "nres" := merge_aux "nl1" "nl2" in
  ("pres", "nres").

Definition eval_state_aux : val :=
  λ: "st", list_fold (λ: "acc" "x", "acc" + "x") #0 "st".

Definition eval_state : val :=
  λ: "st",
  let: "pl" := Fst "st" in
  let: "nl" := Snd "st" in
  let: "eval_pos" := eval_state_aux "pl" in
  let: "eval_neg" := eval_state_aux "nl" in
  "eval_pos" - "eval_neg".

Definition init_st : val := λ: <>, ([], []).

Definition counter_crdt : val := λ: <>, (init_st, mutator, merge).

Definition st_ser :=
  prod_serializer (list_serializer int_serializer)
  (list_serializer int_serializer).

Definition counter_init : val :=
  λ: "addrs" "rid",
  let: "initRes" := statelib_init st_ser.(s_ser) st_ser.(s_deser) "addrs"
                    "rid" counter_crdt in
  let: "get_state" := Fst "initRes" in
  let: "update" := Snd "initRes" in
  let: "eval" := λ: <>,
  eval_state ("get_state" #()) in
  ("eval", "update").
