From aneris.aneris_lang Require Import ast aneris_lifting.
From aneris.aneris_lang.lib Require Import list_code.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_code.
From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.examples.crdt.spec Require Import crdt_base.
From aneris.examples.crdt.statelib.examples.gcounter
     Require Import gcounter_code_wrapper.
From aneris.examples.crdt.statelib.examples.prod_comb
     Require Import prod_comb_code.

Section pn_cpt_code_wrapper.

  Context `{!CRDT_Params}.

  (**  Step 1. Raw PN counter using product and gcpt crdts.  *)

  Definition pn_cpt_init_st : val :=
    λ: <>, prod_init_st gcpt_init_st gcpt_init_st #().

  Definition pn_cpt_mutator : val :=
    λ: "i" "gs" "op",
   prod_mutator gcpt_mutator gcpt_mutator "i" "gs" "op".

  Definition pn_cpt_merge : val :=
  λ: "st1" "st2", prod_merge gcpt_merge gcpt_merge "st1" "st2".

  Definition pn_cpt_crdt : val :=
    λ: <>, prod_crdt gcpt_crdt gcpt_crdt #().

  Definition pn_cpt_init : val :=
    λ: "addrs" "rid",
      prod_init
        vect_serialize vect_deserialize
        vect_serialize vect_deserialize
        gcpt_crdt gcpt_crdt "addrs" "rid".

  (**  Step 2. PN counter wrapper.  *)

  Definition list_int_sum : val :=
    λ: "l", list_fold (λ: "acc" "n", "acc" + "n") #0 "l".


  Definition pncounter_update : val :=
    λ: "upd" "n",
      (if: #0 ≤ "n"
       then  "upd" ("n", #0)
       else  "upd" (#0, (- "n"))).

  Definition pncounter_eval : val :=
    λ: "get_state" <>,
       let: "st" := "get_state" #() in
       let: "pl" := Fst "st" in
       let: "nl" := Snd "st" in
       let: "p" := list_int_sum "pl" in
       let: "n" := list_int_sum "nl" in
       "p" - "n".

 Definition pncounter_init : val :=
    λ: "addrs" "rid",
     let: "pn_cpt" := pn_cpt_init "addrs" "rid" in
     let: "get_st" := Fst "pn_cpt" in
     let: "upd_st" := Snd "pn_cpt" in
     let: "get" := (λ: <>, pncounter_eval "get_st" #()) in
     let: "upd" :=  (λ: "n", pncounter_update "upd_st" "n") in ("get", "upd").

End pn_cpt_code_wrapper.
