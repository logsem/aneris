From Coq Require Import ssreflect.
From stdpp Require Import base gmap.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang.lib Require Import list_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import aneris_lifting proofmode.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_denot crdt_resources.
From aneris.examples.crdt.oplib Require Import oplib_code.
From aneris.examples.crdt.oplib.spec Require Import model spec.
From aneris.examples.crdt.oplib.examples.pncounter Require Import pncounter_code.

(** A positive-negative counter *)
Section PNCounterCrdt.

  Inductive CtrOp :=
  | Add (z : Z) : CtrOp. (* note we can add a negative number *)

  Definition ctr_payload (op : CtrOp) : Z :=
    match op with
    | Add z => z
    end.

  Global Instance ctr_op_eqdecision : EqDecision CtrOp.
  Proof. solve_decision. Qed.

  Global Instance ctr_op_countable : Countable CtrOp.
  Proof.
    refine {|
      encode op := match op with Add z => encode z end;
      decode n := Add <$> @decode Z _ _ n;
    |}.
    intros []. rewrite decode_encode /=. done.
  Qed.

  Definition CtrSt := Z.
  Context `{!Log_Time}.

  (* The value of a counter is just the sum of the operations' payloads. *)
  Fixpoint ctr_value (s : list (Event CtrOp)) : Z :=
    match s with
    | [] => 0%Z
    | ev :: xs => (ctr_payload ev.(EV_Op) + ctr_value xs)%Z
    end.

  Definition ctr_denot (s : gset (Event CtrOp)) (st : CtrSt) : Prop :=
    st = ctr_value (elements s).

  Global Instance ctr_denot_fun : Rel2__Fun ctr_denot.
  Proof.
    constructor; unfold ctr_denot; intros; subst; done.
  Qed.

  Global Instance ctr_denot_instance : CrdtDenot CtrOp CtrSt := {
    crdt_denot := ctr_denot;
  }.
End PNCounterCrdt.

Section OpPNCounter.

  Context `{!Log_Time}.

  Definition op_ctr_effect st (ev : Event CtrOp) st' :=
    st' = (st + ctr_payload ev.(EV_Op))%Z.

  Lemma op_ctr_effect_fun st : Rel2__Fun (op_ctr_effect st).
  Proof.
    constructor. unfold op_ctr_effect.
    intros a b b' Hb Hb'.
    destruct (EV_Op a) as [z]; simpl in *; subst; auto.
  Qed.

  Lemma ctr_value_singleton ev :
    ctr_value [ev] = ctr_payload (ev.(EV_Op)).
  Proof.
    unfold ctr_value. lia.
  Qed.

  Lemma ctr_value_cons ev l :
    ctr_value (ev :: l) = (ctr_payload ev.(EV_Op) + ctr_value l)%Z.
  Proof.
    simpl. auto.
  Qed.

  Lemma ctr_value_app (l l' : list (Event CtrOp)) :
    ctr_value (l ++ l') = (ctr_value l + ctr_value l')%Z.
  Proof.
    generalize dependent l'.
    induction l as [ | h t Ht]; intros l'; [done |].
    rewrite -app_comm_cons.
    do 2 rewrite ctr_value_cons.
    rewrite (Ht l'). lia.
  Qed.

  Lemma ctr_value_perm (l l' : list (Event CtrOp)) :
    Permutation l l' -> ctr_value l = ctr_value l'.
  Proof.
    generalize dependent l'.
    induction l as [ | h t Ht]; intros l' Hperm.
    - apply Permutation_nil in Hperm; subst; reflexivity.
    - rewrite ctr_value_cons.
      apply Permutation_sym in Hperm.
      pose proof Hperm as Hperm'.
      apply Permutation_vs_cons_inv in Hperm as [l1 [l2 ->]].
      apply Permutation_sym, Permutation_cons_app_inv, Ht in Hperm'.
      rewrite Hperm'.
      do 2 rewrite ctr_value_app.
      rewrite ctr_value_cons.
      lia.
  Qed.

  Lemma ctr_denot_union (s : gset (Event CtrOp)) (ev : Event CtrOp) (res : CtrSt) :
    ⟦ s ⟧ ⇝ res ->
    ev ∉ s ->
    ⟦ s ∪ {[ ev ]} ⟧ ⇝ (res + ctr_payload ev.(EV_Op))%Z.
  Proof.
    simpl. unfold ctr_denot.
    intros -> Hnotin.
    assert (s ## {[ ev ]}) as Hdisj by set_solver.
    pose proof (elements_disj_union s
                                    ({[ev]} : gset (Event CtrOp))
                                    Hdisj) as Hperm.
    apply ctr_value_perm in Hperm. rewrite Hperm.
    by rewrite elements_singleton ctr_value_app ctr_value_singleton.
  Qed.

  Instance op_ctr_effect_coh : OpCrdtEffectCoh op_ctr_effect.
  Proof.
    intros s e st st'.
    intros Hdenot Hnotin. split.
    - intros Heff.
      unfold op_ctr_effect in Heff; subst.
      by apply ctr_denot_union.
    - intros Hdenot'.
      unfold op_ctr_effect.
      pose proof (ctr_denot_union s e st Hdenot Hnotin) as Hunion.
      pose proof (rel2_fun Hdenot' Hunion) as Hequiv.
      apply leibniz_equiv in Hequiv; subst; done.
  Qed.

  Definition op_ctr_init_st := 0%Z.

  Lemma op_ctr_init_st_coh : ⟦ (∅ : gset (Event CtrOp)) ⟧ ⇝ op_ctr_init_st.
  Proof. done. Qed.

  Global Instance op_ctr_model_instance : OpCrdtModel CtrOp CtrSt := {
    op_crdtM_effect := op_ctr_effect;
    op_crdtM_effect_fun := op_ctr_effect_fun;
    op_crdtM_effect_coh := op_ctr_effect_coh;
    op_crdtM_init_st := op_ctr_init_st;
    op_crdtM_init_st_coh := op_ctr_init_st_coh
  }.

End OpPNCounter.

From aneris.examples.crdt.oplib.proof Require Import time.

Section PNCounter_proof.
  Context `{!anerisG M Σ}.

  Context `{!CRDT_Params, !OpLib_Res CtrOp}.

  Definition Ctr_OpLib_Op_Coh := λ (op : CtrOp) v, match op with Add z => v = #z end.

  Lemma Ctr_OpLib_Op_Coh_Inj (o1 o2 : CtrOp) (v : val) :
    Ctr_OpLib_Op_Coh o1 v → Ctr_OpLib_Op_Coh o2 v → o1 = o2.
  Proof. destruct o1; destruct o2; simpl; intros ? ?; simplify_eq; done. Qed.

  Lemma Ctr_OpLib_Coh_Ser (op : CtrOp) (v : val) :
    Ctr_OpLib_Op_Coh op v → Serializable int_serialization v.
  Proof.
    destruct op; rewrite /Ctr_OpLib_Op_Coh; intros ?; simplify_eq; apply _.
  Qed.

  Definition Ctr_OpLib_State_Coh := λ (st : CtrSt) v, v = #st.

  Global Instance Ctr_OpLib_Params : OpLib_Params CtrOp CtrSt :=
  {|
    OpLib_Serialization := int_serialization;
    OpLib_State_Coh := Ctr_OpLib_State_Coh;
    OpLib_Op_Coh := Ctr_OpLib_Op_Coh;
    OpLib_Op_Coh_Inj := Ctr_OpLib_Op_Coh_Inj;
    OpLib_Coh_Ser := Ctr_OpLib_Coh_Ser
  |}.

  Lemma Ctr_init_st_fn_spec : ⊢ init_st_fn_spec pncounter_init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /pncounter_init_st.
    wp_pures.
    iApply "HΦ"; done.
  Qed.

  Lemma Ctr_effect_spec : ⊢ effect_spec pncounter_effect.
  Proof.
    iIntros (addr ev st s log_ev log_st).
    iIntros "!#" (Φ) "(%Hev & %Hst & %Hs & %Hevs) HΦ".
    rewrite /pncounter_effect.
    destruct log_ev as [[op] orig vc].
    destruct Hev as (evpl&evvc&evorig&?&Hevpl&?&?).
    rewrite /OpLib_State_Coh /=  /Ctr_OpLib_State_Coh in Hst.
    simplify_eq/=.
    wp_pures.
    iApply "HΦ"; eauto.
  Qed.

  Lemma Ctr_crdt_fun_spec : ⊢ crdt_fun_spec pncounter_crdt.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /pncounter_crdt.
    wp_pures.
    iApply "HΦ".
    iExists _, _; iSplit; first done.
    iSplit; [iApply Ctr_init_st_fn_spec|iApply Ctr_effect_spec].
  Qed.

  Lemma Ctr_init_spec :
    init_spec (oplib_init
               (s_ser (s_serializer OpLib_Serialization))
               (s_deser (s_serializer OpLib_Serialization))) -∗
    init_spec_for_specific_crdt pncounter_init.
  Proof.
    iIntros "#Hinit" (repId addr fixedAddrs addrs_val).
    iIntros (Φ) "!# (%Haddrs & %Hrepid & %Haddr & Hfx & Hprotos & Hskt & Hfr & Htoken) HΦ".
    rewrite /pncounter_init.
    wp_pures.
    wp_apply ("Hinit" with "[$Hfx $Hprotos $Htoken $Hskt $Hfr]").
    { do 3 (iSplit; first done). iApply Ctr_crdt_fun_spec; done. }
    iIntros (get update) "(HLS & #Hget & #Hupdate)".
    wp_pures.
    iApply "HΦ"; eauto.
  Qed.

End PNCounter_proof.
