From Coq Require Import ssreflect Vector.
From stdpp Require Import base gmap vector.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import gset_map.
From aneris.prelude Require Import misc strings.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import network_util_proof.
From aneris.aneris_lang.lib Require Import list_proof set_proof .
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import aneris_lifting proofmode.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_code vector_clock_proof.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_denot crdt_resources.
From aneris.examples.crdt.statelib.user_model
     Require Import semi_join_lattices model params.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.STS Require Import lst.
From aneris.examples.crdt.statelib.proof
     Require Import events spec.
From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.examples.crdt.statelib.examples.gcounter
     Require Import gcounter_code_wrapper gcounter_proof.
From aneris.examples.crdt.statelib.examples.prod_comb
     Require Import prod_comb_code prod_comb_proof.
From aneris.examples.crdt.statelib.examples.pncounter
     Require Import pncounter_code_wrapper.

Section pn_cpt_proof.
  Context `{!anerisG M Σ, !CRDT_Params, !StLib_Res (prodOp gctr_op gctr_op)}.

  Notation pnOp := (prodOp gctr_op gctr_op).
  Notation pnSt := (prodSt gctr_st gctr_st).
  Notation pnParams := (prod_params gctr_op gctr_st gctr_op gctr_st).

  Lemma pn_init_st_fn_spec :
    ⊢ @init_st_fn_spec _ _ _ _ _ _ _ _ _ pnParams pn_cpt_init_st.
  Proof.
    iApply (prod_init_st_fn_spec $! gctr_init_st_fn_spec gctr_init_st_fn_spec).  Qed.

  Lemma pn_cpt_mutator_spec :
    ⊢ @mutator_spec _ _ _ _ _ _ _ _ _ pnParams pn_cpt_mutator.
  Proof.
    by iApply (prod_mutator_st_spec $! gctr_mutator_spec gctr_mutator_spec).
  Qed.

  Lemma pn_cpt_merge_spec :
    ⊢ @merge_spec _ _ _ _ _ _ _ _ _ pnParams pn_cpt_merge.
  Proof.
    by iApply (prod_merge_st_spec $! gctr_merge_spec gctr_merge_spec).
  Qed.

  Lemma pn_crdt_fun_spec :
    ⊢ @crdt_fun_spec _ _ _ _ _ _ _ _ _ pnParams pn_cpt_crdt.
  Proof.
    iApply (prod_crdt_fun_spec $! gctr_crdt_fun_spec gctr_crdt_fun_spec).
  Qed.

  Lemma pn_init_spec :
    @init_spec
      _ _ _ _ _ _ _ _ _ pnParams _
      (statelib_init
         (prod_ser
            (gctr_params.(StLib_StSerialization).(s_serializer)).(s_ser)
            (gctr_params.(StLib_StSerialization).(s_serializer)).(s_ser))
         (prod_deser
            (gctr_params.(StLib_StSerialization).(s_serializer)).(s_deser)
            (gctr_params.(StLib_StSerialization).(s_serializer)).(s_deser))) -∗
    @init_spec_for_specific_crdt
      _ _ _ _ _ _ _ _ _ pnParams _
       pn_cpt_init.
  Proof.
    iIntros "#Hinit".
    by iApply (prod_init_spec $! gctr_crdt_fun_spec gctr_crdt_fun_spec with "[$Hinit]").
  Qed.

End pn_cpt_proof.

Section pncounter_proof.

  Context `{!anerisG M Σ, !CRDT_Params, pnRes : !StLib_Res (prodOp gctr_op gctr_op)}.

  Notation pnOp := (prodOp gctr_op gctr_op).
  Notation pnSt := (prodSt gctr_st gctr_st).
  Notation pnParams := (prod_params gctr_op gctr_st gctr_op gctr_st).

  Lemma wp_list_int_sum (l : list nat) lv ip :
    {{{ ⌜is_list l lv⌝ }}}
      list_int_sum lv  @[ip]
    {{{ (n : nat),  RET #n; ⌜n = list_sum l⌝ }}}.
  Proof.
    iIntros (Φ) "%Hlst HΦ".
    rewrite /list_int_sum. wp_lam. wp_pure _.
    iApply (@wp_list_fold _ _ _ _ _
                (λ (l0 : list nat) (acc : val), ⌜∃ (n : nat), acc = #n ∧ n = list_sum l0⌝)%I
                (λ n, True)%I (λ n, True)%I ip (λ: "acc" "n", "acc" + "n") l #0 lv with "[] []").
    - iIntros (n nv lacc lrem) "!#".
      iIntros (Ψ) "(%Hl & ((%m & -> & ->) & _)) HΨ".
      wp_pures.
      iApply "HΨ".
      iPureIntro. split; last done.
       replace (list_sum lacc + n)%Z with ((list_sum lacc + n)%nat : Z); last lia.
       exists ((list_sum lacc + n)). split; eauto with lia.
       rewrite list_sum_app. simpl. eauto with lia.
    - iPureIntro. simpl. split_and!; try eauto. exists 0; done.
    - iModIntro. iIntros (v) "((%n & -> & ->) & _)".
      by iApply "HΦ".
  Qed.

  Notation pn_upd_spec := (@update_spec _ _ _ pnOp _ _ pnSt _ _ pnParams pnRes).
  Notation pn_get_state_spec := (@get_state_spec _ _ _ pnOp _ _ pnSt _ _ pnParams pnRes).



  (* TODO: Prove: *)
  (* Definition pncounter_update : val := *)
  (*   λ: "upd" "n", *)
  (*     (if: #0 ≤ "n" *)
  (*      then  "upd" ("n", #0) *)
  (*      else  "upd" (#0, (- "n"))). *)

  (* NB: this is not what we want in the end. We want rather an
     @update_spec with a logical state being Z. *)
  Lemma pncounter_update_spec (upd_fn : val) (n : Z) repId addr:
    pn_upd_spec upd_fn repId addr -∗
    {{{ ⌜True⌝ }}}
      pncounter_update upd_fn #n @[ip_of_address addr]
    {{{ (n : nat),  RET #n; ⌜n = n⌝ }}}.
  Proof. Admitted.


  (* TODO: Prove: *)
  (* Definition pncounter_eval : val := *)
  (*   λ: "get_state" <>, *)
  (*      let: "st" := "get_state" #() in *)
  (*      let: "pl" := Fst "st" in *)
  (*      let: "nl" := Snd "st" in *)
  (*      let: "p" := list_int_sum "pl" in *)
  (*      let: "n" := list_int_sum "nl" in *)
  (*      "p" - "n". *)

 (* NB: this is not what we want in the end. We want rather an
     @get_state_spec with a logical state being Z. *)
  Lemma pncounter_eval_spec (get_state_fn : val) repId addr:
    pn_get_state_spec get_state_fn repId addr -∗
    {{{ ⌜True⌝ }}}
      pncounter_eval get_state_fn #() @[ip_of_address addr]
    {{{ (n : nat),  RET #n; ⌜n = n⌝ }}}.
  Proof. Admitted.

  (* TODO: Prove: *)
  (* Definition pncounter_init : val := *)
  (*   λ: "addrs" "rid", *)
  (*     let: "pn_cpt" := pn_cpt_init "addrs" "rid" in *)
  (*     let: "get_st" := Fst "pn_cpt" in *)
  (*     let: "upd_st" := Snd "pn_cpt" in *)
  (*     let: "get" := pncounter_eval "get_st" in *)
  (*     let: "upd" := pncounter_update "upd_st" in *)
  (*     ("get", "upd"). *)

End pncounter_proof.
