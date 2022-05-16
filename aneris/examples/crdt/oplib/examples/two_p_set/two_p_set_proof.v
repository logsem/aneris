From Coq Require Import ssreflect.
From stdpp Require Import base gmap.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import gset_map.
From aneris.aneris_lang.lib Require Import list_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import aneris_lifting proofmode.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_denot crdt_resources.
From aneris.examples.crdt.oplib Require Import oplib_code.
From aneris.examples.crdt.oplib.spec Require Import model spec.
From aneris.examples.crdt.oplib.examples.two_p_set Require Import two_p_set_code.

Section tpsCrdt.
  Context `{!Log_Time} `{!EqDecision vl} `{!Countable vl}.

  Definition tpsOp : Type := vl + vl.
  Definition tpsSt : Type := gset vl * gset vl.

  Definition update_state (op : tpsOp) (st : tpsSt) : tpsSt :=
    match op with
    | inl a => ({[a]} ∪ st.1, st.2)
    | inr a => (st.1, {[a]} ∪ st.2)
    end.

  Definition tps_denot (s : gset (Event tpsOp)) (state : tpsSt) : Prop :=
    set_fold (λ ev st, update_state (EV_Op ev) st) (∅, ∅) s = state.

  Global Instance tps_denot_fun : Rel2__Fun tps_denot.
  Proof. constructor; intros ? ? ? <- <-; done. Qed.

  Global Instance tps_denot_instance : CrdtDenot tpsOp tpsSt := {
    crdt_denot := tps_denot;
  }.
End tpsCrdt.

Global Arguments tpsOp _ : clear implicits.
Global Arguments tpsSt _ {_ _}.

Section OpTps.
  Context `{!Log_Time}
          `{!EqDecision vl} `{!Countable vl}.

  Definition op_tps_effect (st : tpsSt vl) (ev : Event (tpsOp vl)) (st' : tpsSt vl) : Prop :=
    st' = update_state (EV_Op ev) st.

  Lemma op_tps_effect_fun st : Rel2__Fun (op_tps_effect st).
  Proof. constructor; intros ??? -> ->; done. Qed.

  Instance op_tps_effect_coh : OpCrdtEffectCoh op_tps_effect.
  Proof.
    intros s ev st st' Hst Hevs Hmax Hext.
    rewrite /op_tps_effect /crdt_denot /= /tps_denot.
    rewrite set_fold_disj_union_strong; [| |set_solver]; last first.
    { intros [[] ] [[] ]; rewrite /update_state /=; intros; f_equal; set_solver. }
    rewrite Hst set_fold_singleton; split; done.
  Qed.

  Definition op_tps_init_st : tpsSt vl := (∅, ∅).

  Lemma op_tps_init_st_coh : ⟦ (∅ : gset (Event (tpsOp vl))) ⟧ ⇝ op_tps_init_st.
  Proof. done. Qed.

  Global Instance op_tps_model_instance : OpCrdtModel (tpsOp vl) (tpsSt vl) := {
    op_crdtM_effect := op_tps_effect;
    op_crdtM_effect_fun := op_tps_effect_fun;
    op_crdtM_effect_coh := op_tps_effect_coh;
    op_crdtM_init_st := op_tps_init_st;
    op_crdtM_init_st_coh := op_tps_init_st_coh
  }.

End OpTps.

From aneris.aneris_lang.lib Require Import set_code set_proof.
From aneris.aneris_lang.lib Require Import inject.
From aneris.examples.crdt.oplib.proof Require Import time.

Section tps_proof.
  Context `{!EqDecision vl} `{!Countable vl}
          `{!Inject vl val} `{!∀ (a : vl), Serializable vl_serialization $a}.

  Context `{!anerisG M Σ}.

  Context `{!CRDT_Params} `{!OpLib_Res (tpsOp vl)}.

  Definition tps_OpLib_Op_Coh := λ (op : tpsOp vl) (v : val), v = $op.

  Lemma tps_OpLib_Op_Coh_Inj (o1 o2 : tpsOp vl) (v : val) :
    tps_OpLib_Op_Coh o1 v → tps_OpLib_Op_Coh o2 v → o1 = o2.
  Proof. intros Ho1 Ho2; apply (inj (@inject _ _ Inject_sum)); rewrite -Ho1 -Ho2; done. Qed.

  Lemma tps_OpLib_Coh_Ser (op : tpsOp vl) (v : val) :
    tps_OpLib_Op_Coh op v → Serializable (sum_serialization vl_serialization vl_serialization) v.
  Proof. intros Heq. rewrite Heq; destruct op; apply _. Qed.

  Definition tps_OpLib_State_Coh :=
    λ (st : tpsSt vl) v, ∃ v1 v2, v = PairV v1 v2 ∧ is_set st.1 v1 ∧ is_set st.2 v2.

  Global Instance tps_OpLib_Params : OpLib_Params (tpsOp vl) (tpsSt vl) :=
  {|
    OpLib_Serialization := (sum_serialization vl_serialization vl_serialization);
    OpLib_State_Coh := tps_OpLib_State_Coh;
    OpLib_Op_Coh := tps_OpLib_Op_Coh;
    OpLib_Op_Coh_Inj := tps_OpLib_Op_Coh_Inj;
    OpLib_Coh_Ser := tps_OpLib_Coh_Ser
  |}.

  Lemma tps_init_st_fn_spec : ⊢ init_st_fn_spec init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /init_st.
    wp_pures.
    wp_apply wp_set_empty; first done.
    iIntros (v Hv).
    wp_apply wp_set_empty; first done.
    iIntros (w Hw).
    wp_pures.
    iApply "HΦ".
    iPureIntro; eexists _, _; split_and!; simpl; done.
  Qed.

  Lemma tps_effect_spec : ⊢ effect_spec effect.
  Proof.
    iIntros (addr ev st s log_ev log_st).
    iIntros "!#" (Φ) "(%Hev & %Hst & %Hs & %Hevs) HΦ".
    rewrite /effect.
    destruct log_ev as [log_ev orig vc].
    destruct Hev as (evpl&evvc&evorig& ?&Hopcoh&?&?).
    destruct Hevs as (Hnin & Hmax & Hext).
    destruct log_st as [log_st1 log_st2].
    destruct Hst as (st1&st2&?&?&?).
    simplify_eq/=.
    rewrite Hopcoh /=.
    wp_pures.
    destruct log_ev; wp_pures.
    - wp_apply wp_set_add; first by iPureIntro.
      iIntros (w Hw).
      wp_pures.
      iApply "HΦ".
      iExists _; iSplit; last by eauto.
      simpl; iPureIntro; eexists _, _; split_and!; done.
    - wp_apply wp_set_add; first by iPureIntro.
      iIntros (w Hw).
      wp_pures.
      iApply "HΦ".
      iExists _; iSplit; last by eauto.
      simpl; iPureIntro; eexists _, _; split_and!; done.
  Qed.

  Lemma tps_crdt_fun_spec : ⊢ crdt_fun_spec tps_crdt.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /tps_crdt.
    wp_pures.
    iApply "HΦ".
    iExists _, _; iSplit; first done.
    iSplit.
    - iApply tps_init_st_fn_spec; done.
    - iApply tps_effect_spec; done.
  Qed.

  Lemma tps_init_spec :
    init_spec
      (oplib_init
         (s_ser (s_serializer (sum_serialization vl_serialization vl_serialization)))
         (s_deser (s_serializer (sum_serialization vl_serialization vl_serialization)))) -∗
    init_spec_for_specific_crdt
      (tps_init (s_ser (s_serializer vl_serialization)) (s_deser (s_serializer vl_serialization))).
  Proof.
    iIntros "#Hinit" (repId addr fixedAddrs addrs_val).
    iIntros (Φ) "!# (%Haddrs & %Hrepid & %Haddr & Hfx & Hprotos & Hskt & Hfr & Htoken) HΦ".
    rewrite /tps_init.
    wp_pures.
    wp_apply ("Hinit" with "[$Hfx $Hprotos $Htoken $Hskt $Hfr]").
    { do 3 (iSplit; first done). iApply tps_crdt_fun_spec; done. }
    iIntros (get update) "(HLS & #Hget & #Hupdate)".
    wp_pures.
    iApply "HΦ"; eauto.
  Qed.

End tps_proof.
