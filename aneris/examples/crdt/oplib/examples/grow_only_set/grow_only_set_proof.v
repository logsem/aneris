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
From aneris.examples.crdt.oplib.examples.grow_only_set Require Import grow_only_set_code.

Section gosCrdt.
  Context `{!Log_Time} `{!EqDecision vl} `{!Countable vl}.

  Definition gosOp : Type := vl.
  Definition gosSt : Type := gset vl.

  Definition gos_denot (s : gset (Event gosOp)) (state : gosSt) : Prop :=
    gset_map EV_Op s = state.

  Global Instance gos_denot_fun : Rel2__Fun gos_denot.
  Proof. constructor; intros ? ? ? <- <-; done. Qed.

  Global Instance gos_denot_instance : CrdtDenot gosOp gosSt := {
    crdt_denot := gos_denot;
  }.
End gosCrdt.

Global Arguments gosOp _ : clear implicits.
Global Arguments gosSt _ {_ _}.

Section OpGos.
  Context `{!Log_Time}
          `{!EqDecision vl} `{!Countable vl}.

  Definition op_gos_effect (st : gosSt vl) (ev : Event (gosOp vl)) (st' : gosSt vl) : Prop :=
    st' = {[EV_Op ev]} ∪ st.

  Lemma op_gos_effect_fun st : Rel2__Fun (op_gos_effect st).
  Proof. constructor; intros ??? -> ->; done. Qed.

  Instance op_gos_effect_coh : OpCrdtEffectCoh op_gos_effect.
  Proof.
    intros s ev st st' Hst Hevs Hmax Hext.
    rewrite /op_gos_effect /crdt_denot /= /gos_denot gset_map_union gset_map_singleton Hst.
    clear; set_solver.
  Qed.

  Definition op_gos_init_st : gosSt vl := ∅.

  Lemma op_gos_init_st_coh : ⟦ (∅ : gset (Event (gosOp vl))) ⟧ ⇝ op_gos_init_st.
  Proof. done. Qed.

  Global Instance op_gos_model_instance : OpCrdtModel (gosOp vl) (gosSt vl) := {
    op_crdtM_effect := op_gos_effect;
    op_crdtM_effect_fun := op_gos_effect_fun;
    op_crdtM_effect_coh := op_gos_effect_coh;
    op_crdtM_init_st := op_gos_init_st;
    op_crdtM_init_st_coh := op_gos_init_st_coh
  }.

End OpGos.

From aneris.aneris_lang.lib Require Import set_code set_proof.
From aneris.aneris_lang.lib Require Import inject.
From aneris.examples.crdt.oplib.proof Require Import time.

Section gos_proof.
  Context `{!EqDecision vl} `{!Countable vl}
          `{!Inject vl val} `{!∀ (a : vl), Serializable vl_serialization $a}.

  Context `{!anerisG M Σ}.

  Context `{!CRDT_Params} `{!OpLib_Res (gosOp vl)}.

  Definition gos_OpLib_Op_Coh :=
    λ (op : gosOp vl) v, v = $op.

  Lemma gos_OpLib_Op_Coh_Inj (o1 o2 : gosOp vl) (v : val) :
    gos_OpLib_Op_Coh o1 v → gos_OpLib_Op_Coh o2 v → o1 = o2.
  Proof. intros Ho1 Ho2; apply (inj inject); rewrite -Ho1 -Ho2; done. Qed.

  Lemma gos_OpLib_Coh_Ser (op : gosOp vl) (v : val) :
    gos_OpLib_Op_Coh op v → Serializable vl_serialization v.
  Proof. intros ->; apply _. Qed.

  Definition gos_OpLib_State_Coh := λ (st : gosSt vl) v, is_set st v.

  Global Instance gos_OpLib_Params : OpLib_Params (gosOp vl) (gosSt vl) :=
  {|
    OpLib_Serialization := vl_serialization;
    OpLib_State_Coh := gos_OpLib_State_Coh;
    OpLib_Op_Coh := gos_OpLib_Op_Coh;
    OpLib_Op_Coh_Inj := gos_OpLib_Op_Coh_Inj;
    OpLib_Coh_Ser := gos_OpLib_Coh_Ser
  |}.

  Lemma gos_init_st_fn_spec : ⊢ init_st_fn_spec init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /init_st.
    wp_pures.
    wp_apply wp_set_empty; first done.
    iIntros (v Hv).
    iApply "HΦ".
    iPureIntro; apply Hv.
  Qed.

  Lemma gos_effect_spec : ⊢ effect_spec effect.
  Proof.
    iIntros (addr ev st s log_ev log_st).
    iIntros "!#" (Φ) "(%Hev & %Hst & %Hs & %Hevs) HΦ".
    rewrite /effect.
    destruct log_ev as [log_ev orig vc].
    destruct Hev as (evpl&evvc&evorig& ?&Hopcoh&?&?).
    destruct Hevs as (Hnin & Hmax & Hext).
    simplify_eq.
    rewrite Hopcoh /=.
    wp_pures.
    wp_apply wp_set_add; first by iPureIntro; apply Hst.
    iIntros (w Hw).
    iApply "HΦ".
    iExists _; done.
  Qed.

  Lemma gos_crdt_fun_spec : ⊢ crdt_fun_spec gos_crdt.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /gos_crdt.
    wp_pures.
    iApply "HΦ".
    iExists _, _; iSplit; first done.
    iSplit.
    - iApply gos_init_st_fn_spec; done.
    - iApply gos_effect_spec; done.
  Qed.

  Lemma prod_init_spec :
    init_spec
      (oplib_init
         (s_ser (s_serializer vl_serialization)) (s_deser (s_serializer vl_serialization))) -∗
    init_spec_for_specific_crdt
      (gos_init (s_ser (s_serializer vl_serialization)) (s_deser (s_serializer vl_serialization))).
  Proof.
    iIntros "#Hinit" (repId addr fixedAddrs addrs_val).
    iIntros (Φ) "!# (%Haddrs & %Hrepid & %Haddr & Hfx & Hprotos & Hskt & Hfr & Htoken) HΦ".
    rewrite /gos_init.
    wp_pures.
    wp_apply ("Hinit" with "[$Hfx $Hprotos $Htoken $Hskt $Hfr]").
    { do 3 (iSplit; first done). iApply gos_crdt_fun_spec; done. }
    iIntros (get update) "(HLS & #Hget & #Hupdate)".
    wp_pures.
    iApply "HΦ"; eauto.
  Qed.

End gos_proof.
