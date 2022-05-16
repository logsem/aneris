From Coq Require Import ssreflect.
From stdpp Require Import base gmap.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang.lib Require Import list_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import aneris_lifting proofmode.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_denot crdt_resources.
From aneris.examples.crdt.oplib Require Import oplib_code.
From aneris.examples.crdt.oplib.spec Require Import model spec.
From aneris.examples.crdt.oplib.examples.mvreg Require Import mvreg_code.

(** Multi-value Register *)
Section MVRegister.

  Inductive MVOp : Type :=
  | Write (z : Z) : MVOp.

  Definition mv_payload (op : MVOp) : Z :=
    match op with
    | Write z => z
    end.

  Global Instance mv_op_eqdecision : EqDecision MVOp.
  Proof. solve_decision. Qed.

  Global Instance mv_op_countable : Countable MVOp.
  Proof.
    refine {|
      encode op := match op with Write z => encode z end;
      decode n := Write <$> @decode Z _ _ n;
    |}.
    intros []. rewrite decode_encode /=. done.
  Qed.

  Context `{!Log_Time}.

  (* The state of the multi-value register is the set of (value, timestamp)
     pairs in it.
     There can be more than one because two concurrent writes don't overwrite
     each other.
     In other words, the register stores the values of all concurrent writes. *)
  Definition MVStElem : Type := Z * Time.
  Definition MVSt : Type := gset MVStElem.

  Definition mv_coh (ev : Event MVOp) (v : MVStElem) : Prop :=
    match v with
    | (val, ts) =>
      mv_payload ev.(EV_Op) = val /\ time ev = ts
    end.

  Definition mv_denot (s : gset (Event MVOp)) (st : MVSt) : Prop :=
    ∀ v, v ∈ st <->
         ∃ wr, wr ∈ s ∧ mv_coh wr v ∧ maximal wr s.

  Global Instance mv_denot_fun : Rel2__Fun mv_denot.
  Proof.
    constructor; unfold mv_denot.
    intros a b b' Hab Hab'.
    apply leibniz_equiv.
    intros x; split; intros Hin.
    - apply Hab in Hin as [wr Hwr].
      apply (iffRL (Hab' x)).
      eauto.
    - apply Hab' in Hin as [wr Hwr].
      apply (iffRL (Hab x)).
      eauto.
  Qed.

  Global Instance mv_denot_instance : CrdtDenot MVOp MVSt :=
    { crdt_denot := mv_denot }.

End MVRegister.

Section OpMVRegister.

  Context `{H: !Log_Time}.

  Global Instance mv_st_elem_timed : Timed MVStElem := snd.

  Definition op_mv_register_effect (st : MVSt) (ev : Event MVOp) (st' : MVSt) : Prop :=
    let elem := (mv_payload ev.(EV_Op), time ev) in
      st' = {[ elem ]} ∪ filter (λ elem', not (elem' <_t elem)) st.

  Lemma op_mv_register_effect_fun st : Rel2__Fun (op_mv_register_effect st).
  Proof.
    constructor.
    unfold op_mv_register_effect.
    intros ev st1 st2 -> ->.
    done.
  Qed.

  Instance op_mv_register_effect_coh : OpCrdtEffectCoh op_mv_register_effect.
  Proof.
    intros s ev st st' Hdenot Hnotin Hmax Hevs_ext.
    rewrite /op_mv_register_effect /crdt_denot /= /mv_denot.
    split.
    - intros ->.
      intros v; rewrite elem_of_union elem_of_singleton elem_of_filter.
      split.
      + intros [->| [Hvtm Hvst]]; first by exists ev; split_and!; first set_solver.
        apply Hdenot in Hvst as (wr & Hwrs & Hwrv & Hwrmax).
        exists wr; split_and!; [set_solver|done|].
        apply maximal_union; first done.
        destruct v; destruct Hwrv as [? ?]; simplify_eq; done.
      + setoid_rewrite elem_of_union.
        setoid_rewrite elem_of_singleton.
        intros (wr & [Hwrs| ->] & Hwrv & Hwrmax); last first.
        { destruct v; destruct Hwrv as [? ?]; simplify_eq; auto. }
        destruct v; destruct Hwrv as [? ?]; simplify_eq.
        right; split; first by apply Hwrmax; set_solver.
        apply Hdenot; exists wr; split_and!; [done|done|].
        eapply maximal_union_inv; done.
    - intros Hwr; apply set_eq; intros v.
      rewrite Hwr.
      setoid_rewrite elem_of_union.
      setoid_rewrite elem_of_singleton.
      rewrite elem_of_filter.
      split.
      + destruct v.
        intros (wr & [Hwrs| ->] & [] & Hwrmax); simplify_eq; last by eauto.
        right; split; first by apply Hwrmax; set_solver.
        apply Hdenot; exists wr; split_and!; [done|done|].
        eapply maximal_union_inv; done.
      + intros [->|[Hvt Hvst]]; first by exists ev; split_and!; first auto.
        destruct v.
        apply Hdenot in Hvst as (wr' & Hwr's & [] & Hwr'max); simplify_eq.
        exists wr'; split_and!; [auto| |apply maximal_union]; done.
  Qed.

  Definition op_mv_register_init_st : MVSt := ∅.

  Lemma op_mv_register_init_st_coh : ⟦ (∅ : gset (Event MVOp)) ⟧ ⇝ op_mv_register_init_st.
  Proof. intros ?; set_solver. Qed.

  Global Instance op_mv_register_model_instance : OpCrdtModel MVOp MVSt := {
    op_crdtM_effect := op_mv_register_effect;
    op_crdtM_effect_fun := op_mv_register_effect_fun;
    op_crdtM_effect_coh := op_mv_register_effect_coh;
    op_crdtM_init_st := op_mv_register_init_st;
    op_crdtM_init_st_coh := op_mv_register_init_st_coh
  }.

End OpMVRegister.

From aneris.prelude Require Import time.
From aneris.aneris_lang.lib Require Import inject.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.examples.crdt.oplib.proof Require Import time.

Section MVreg_proof.
  Context `{!anerisG M Σ}.

  Context `{!CRDT_Params, !OpLib_Res MVOp}.

  Definition mv_register_OpLib_Op_Coh := λ (op : MVOp) v, match op with Write z => v = #z end.

  Lemma mv_register_OpLib_Op_Coh_Inj (o1 o2 : MVOp) (v : val) :
    mv_register_OpLib_Op_Coh o1 v → mv_register_OpLib_Op_Coh o2 v → o1 = o2.
  Proof. destruct o1; destruct o2; simpl; intros ? ?; simplify_eq; done. Qed.

  Lemma mv_register_OpLib_Coh_Ser (op : MVOp) (v : val) :
    mv_register_OpLib_Op_Coh op v → Serializable int_serialization v.
  Proof.
    destruct op; rewrite /mv_register_OpLib_Op_Coh; intros ?; simplify_eq; apply _.
  Qed.

  (* TODO: move to the right place. *)
  Global Instance vector_clock_inject : Inject vector_clock val :=
    { inject := vector_clock_to_val }.

  Definition mv_register_OpLib_State_Coh (st : MVSt) v : Prop :=
    ∃ (l : list (Z * vector_clock)), is_list l v ∧ ∀ v, v ∈ st ↔ v ∈ l.

  Global Instance Ctr_OpLib_Params : OpLib_Params MVOp MVSt :=
  {|
    OpLib_Serialization := int_serialization;
    OpLib_State_Coh := mv_register_OpLib_State_Coh;
    OpLib_Op_Coh := mv_register_OpLib_Op_Coh;
    OpLib_Op_Coh_Inj := mv_register_OpLib_Op_Coh_Inj;
    OpLib_Coh_Ser := mv_register_OpLib_Coh_Ser
  |}.

  Lemma mv_register_init_st_fn_spec : ⊢ init_st_fn_spec init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /init_st.
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    exists []; split; [done|set_solver].
  Qed.

  (* TODO: moe to the right place; this strengthenes the existing proof. *)
  (* This also changes the API to use filter instead of list.filter. Why whas that choice made!?*)
  Lemma wp_list_filter `{!Inject A val} (l : list A) (P : A -> bool) (f lv : val) ip :
    {{{ (∀ (x : A),
            {{{ ⌜x ∈ l⌝ }}}
              f $x @[ip]
            {{{ w, RET w; ⌜w = $(P x)⌝ }}} ) ∗
        ⌜is_list l lv⌝ }}}
       list_code.list_filter f lv @[ip]
     {{{ rv, RET rv; ⌜is_list (filter P l) rv⌝ }}}.
  Proof.
    iIntros (Φ) "[#Hf %Hil] HΦ".
    iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil.
    - subst.
      rewrite /list_code.list_filter; wp_pures.
      iApply "HΦ"; done.
    - destruct Hil as (lv' & -> & Hil).
      rewrite /list_code.list_filter.
      do 7 (wp_pure _).
      fold list_code.list_filter.
      wp_apply ("IH" $! lv'); [done| |].
      { iIntros "!#" (? ?) "!# %"; iApply "Hf"; iPureIntro; apply elem_of_cons; auto. }
      iIntros (rv) "%Hilp"; wp_pures.
      wp_apply "Hf"; [by iPureIntro; apply elem_of_cons; auto|].
      iIntros (w) "->".
      destruct (P h) eqn:HP; wp_pures.
      + wp_apply wp_list_cons; [by eauto |].
        iIntros (v) "%Hil'".
        iApply "HΦ"; iPureIntro.
        rewrite filter_cons.
        rewrite HP; simpl.
        simpl in Hil'; done.
      + iApply "HΦ"; iPureIntro.
        rewrite filter_cons.
        rewrite HP. done.
  Qed.

  Lemma mv_register_effect_spec : ⊢ effect_spec effect.
  Proof.
    iIntros (addr ev st s log_ev log_st).
    iIntros "!#" (Φ) "(%Hev & %Hst & %Hs & %Hevs) HΦ".
    rewrite /effect.
    destruct log_ev as [[op] orig vc].
    destruct Hev as (evpl&evvc&evorig&?&Hevpl&?&?).
    destruct Hevs as (Hev & Hmax & Hext).
    destruct Hst as (l & Hl & Hlst).
    simplify_eq/=.
    wp_pures.
    wp_apply (wp_list_filter l (λ p, bool_decide (¬ vector_clock_lt p.2 vc))).
    { iSplit; last done.
      iIntros ([z t] Ψ) "!# %Hel HΨ".
      apply Hlst, Hs in Hel as (wr & Hwrs & [] & Hwrmax); simplify_eq.
      assert (time wr ≠ vc).
      { intros <-.
        assert (wr = {| EV_Op := Write op; EV_Orig := orig; EV_Time := time wr |});
            last by destruct wr; simplify_eq/=; set_solver.
          apply Hext; [set_solver|set_solver|done]. }
      simpl.
      do 4 wp_pure _.
      wp_apply assert_proof.wp_assert.
      wp_apply wp_vect_leq; first by iSplit; last by iPureIntro; apply vector_clock_to_val_is_vc.
      iIntros (? ->).
      rewrite /time /=.
      rewrite (bool_decide_eq_false_2 (vector_clock_le _ _)); last first.
      { intros [->|Hvct]%vector_clock_le_eq_or_lt; first done.
        revert Hvct; apply Hmax; set_solver. }
      wp_pures.
      iSplit; first done.
      iNext.
      rewrite /vect_conc.
      wp_pures.
      wp_apply wp_vect_leq; first by iSplit; first by iPureIntro; apply vector_clock_to_val_is_vc.
      iIntros (? ->).
      destruct (decide (vector_clock_le (@time vc_time _ _ wr) vc)) as [Hle|Hnle].
      - rewrite (bool_decide_eq_true_2 (vector_clock_le _ _)); last done.
        wp_pures.
        iApply "HΨ".
        rewrite bool_decide_eq_false_2; first done.
        intros Hvclt; apply Hvclt.
        apply vector_clock_le_eq_or_lt in Hle as [|]; done.
      - rewrite (bool_decide_eq_false_2 (vector_clock_le _ _));
          last by intros ?; apply Hnle; apply vector_clock_lt_le.
        wp_pures.
        wp_apply wp_vect_leq; first by iSplit; last by iPureIntro; apply vector_clock_to_val_is_vc.
        iIntros (? ->).
        wp_pures.
        iApply "HΨ".
        iPureIntro.
        rewrite <- bool_decide_not.
        do 2 f_equal.
        apply bool_decide_ext.
        rewrite /time /=.
        split.
        + intros Hnle' ?%vector_clock_lt_le; apply Hnle'; done.
        + intros Hnlt [|]%vector_clock_le_eq_or_lt; [done|].
          eapply Hmax; last done; set_solver. }
    iIntros (rv Hrv).
    wp_pures.
    replace (#op, evvc)%V with (inject (op, vc) : val); last first.
    { simpl; f_equal. by apply is_vc_vector_clock_to_val. }
    iApply wp_list_cons; first done.
    iNext.
    iIntros (res Hres).
    iApply "HΦ"; iPureIntro.
    simpl; eexists; split; last done; simpl.
    eexists; split; first done.
    intros v.
    rewrite elem_of_union elem_of_singleton elem_of_filter elem_of_cons elem_of_list_filter.
    rewrite /time /=.
    rewrite Hlst bool_decide_spec; done.
  Qed.

  Lemma mv_register_crdt_fun_spec : ⊢ crdt_fun_spec mvreg_crdt.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /mvreg_crdt.
    wp_pures.
    iApply "HΦ".
    iExists _, _; iSplit; first done.
    iSplit; [iApply mv_register_init_st_fn_spec|iApply mv_register_effect_spec].
  Qed.

  Lemma Ctr_init_spec :
    init_spec (oplib_init
               (s_ser (s_serializer OpLib_Serialization))
               (s_deser (s_serializer OpLib_Serialization))) -∗
    init_spec_for_specific_crdt mvreg_init.
  Proof.
    iIntros "#Hinit" (repId addr fixedAddrs addrs_val).
    iIntros (Φ) "!# (%Haddrs & %Hrepid & %Haddr & Hfx & Hprotos & Hskt & Hfr & Htoken) HΦ".
    rewrite /mvreg_init.
    wp_pures.
    wp_apply ("Hinit" with "[$Hfx $Hprotos $Htoken $Hskt $Hfr]").
    { do 3 (iSplit; first done). iApply mv_register_crdt_fun_spec; done. }
    iIntros (get update) "(HLS & #Hget & #Hupdate)".
    wp_pures.
    iApply "HΦ"; eauto.
  Qed.

End MVreg_proof.
