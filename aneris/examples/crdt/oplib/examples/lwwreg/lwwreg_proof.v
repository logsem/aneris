From Coq Require Import ssreflect.
From stdpp Require Import base gmap.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import time.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import aneris_lifting proofmode.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_denot crdt_resources.
From aneris.examples.crdt.oplib Require Import oplib_code.
From aneris.examples.crdt.oplib.spec Require Import model spec.
From aneris.examples.crdt.oplib.examples.lwwreg Require Import lwwreg_code.
From aneris.aneris_lang.lib Require Import inject list_proof.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.examples.crdt.oplib.proof Require Import time.

(** Last-writer-wins register. Ties broken by Lamport timestamp plus origin id. *)
Section LWWRegister.

  Context `{PayloadT : Type}.
  Context `{!EqDecision PayloadT, !Countable PayloadT}.

  Inductive LWWOp : Type :=
  | Write (v : PayloadT) : LWWOp.

  Definition lww_payload (op : LWWOp) : PayloadT :=
    match op with
    | Write v => v
    end.

  Global Instance lww_op_eqdecision : EqDecision LWWOp.
  Proof. solve_decision. Qed.

  Global Instance lww_op_countable : Countable LWWOp.
  Proof.
    refine {|
      encode op := match op with Write v => encode v end;
      decode n := Write <$> @decode _ _ _ n;
    |}.
    intros []. rewrite decode_encode /=. done.
  Qed.

  (* TODO: make the denotation more generic by not depending on vector clocks.
     (Needed if we want to implement with state-based CRDTs). *)

  Fixpoint to_lamport (vc : vector_clock) : nat :=
    match vc with
    | nil => 0
    | h :: t => h + to_lamport t
    end.

  Lemma vector_clock_le_to_lamport_le vc vc' :
    vector_clock_le vc vc' -> to_lamport vc <= to_lamport vc'.
  Proof.
    intros Hle.
    rewrite /vector_clock_le in Hle.
    induction Hle; [done | simpl; lia].
  Qed.

  Lemma vector_clock_lt_to_lamport_lt vc vc' :
    vector_clock_lt vc vc' -> to_lamport vc < to_lamport vc'.
  Proof.
    intros [Hle Hlt].
    induction Hle; [by inversion Hlt |].
    simpl.
    destruct (decide (x = y)) as [-> | Hne].
    - simpl in Hlt.
      inversion Hlt as [ | ? ? Htail]; subst; [exfalso; simpl in *; lia |].
      apply IHHle in Htail; lia.
    - assert (x < y) as ? by lia.
      apply vector_clock_le_to_lamport_le in Hle; lia.
  Qed.

  Definition lww_lt (e e' : Event LWWOp) : Prop :=
    let ts := to_lamport (EV_Time e) in
    let ts' := to_lamport (EV_Time e') in
    (ts < ts') ∨ (ts = ts' ∧ (EV_Orig e) < (EV_Orig e')).

  Global Instance lwwlt_strict : StrictOrder lww_lt.
  Proof.
    constructor.
    - intros e [Hl | [_ Hr]]; [lia | destruct e; lia].
    - intros a b c [Hlt | [Heq Ho]] [Hlt' | [Heq' Ho']]; try (left; lia).
      right; split; lia.
  Qed.

  Definition lww_max (e : Event LWWOp) (s : gset (Event LWWOp)) : Prop :=
    e ∈ s ∧ (∀ e', e' ∈ s -> e' ≠ e -> lww_lt e' e).

  Definition LWWSt : Type := option (Event LWWOp).

  Definition lww_denot (s : gset (Event LWWOp)) (st : LWWSt) : Prop :=
    (s = ∅ ∧ st = None) ∨ (∃ e, st = Some e ∧ events_ext s ∧ lww_max e s).

  Global Instance lww_denot_fun : Rel2__Fun lww_denot.
  Proof.
    constructor; unfold lww_denot.
    intros s b b'.
    intros [[-> ->] |[e [Hbeq [Hext [Hein Hmax]]]]] [[Heq Hb] | [e' (-> & _ & [Hein' Hmax'])]].
    - done.
    - exfalso; set_solver.
    - exfalso.
      rewrite Heq in Hein.
      set_solver.
    - destruct (decide (e = e')) as [-> | Hne]; [done|].
      assert (e' ≠ e) as Hne'; [done|].
      pose proof Hein as Hlwwlt.
      pose proof Hein' as Hlwwlt'.
      apply Hmax in Hlwwlt'; auto.
      apply Hmax' in Hlwwlt; auto.
      destruct Hlwwlt as [He1 | He2]; destruct Hlwwlt' as [He1' | He2'].
     + exfalso; lia.
     + destruct He2' as [Heqt _].
       exfalso; lia.
     + destruct He2 as [? ?].
       exfalso; lia.
     + destruct He2 as [_ Horig].
       destruct He2' as [_ Horig'].
       exfalso; lia.
  Qed.

  Global Instance lww_denot_instance : CrdtDenot LWWOp LWWSt :=
    { crdt_denot := lww_denot }.

End LWWRegister.

Global Arguments LWWOp : clear implicits.

Section OpLWWRegister.

  Context (PT : Type). (* payload type *)
  Context `{!EqDecision PT, !Countable PT}.

  Definition op_lww_register_effect (st : LWWSt) (ev : Event (LWWOp PT)) (st' : LWWSt) : Prop :=
    (st = None ∧ st' = Some ev) ∨
      (∃ e, st = Some e ∧
            ((st' = Some e ∧ lww_lt ev e) ∨
             (st' = Some ev ∧ lww_lt e ev))).

  Lemma op_lww_register_effect_fun st : Rel2__Fun (op_lww_register_effect st).
  Proof.
    constructor.
    unfold op_lww_register_effect.
    intros a b b' [Hl | Hr] [Hl' | Hr'].
    - destruct Hl as [_ ->].
      destruct Hl' as [_ ->].
      done.
    - destruct Hl as [-> ->].
      destruct Hr' as [e [Heq _]].
      exfalso.
      inversion Heq.
    - destruct Hr as [e [-> Hlt]].
      destruct Hl' as [Heq _].
      exfalso.
      inversion Heq.
    - destruct Hr as [e [-> [[-> Hltl] | [Heq Hlt]]]];
      destruct Hr' as [e' [Heqe [[-> Hltl'] | [Heq' Hlt']]]].
      + done.
      + assert (e = e') as ->; [inversion Heqe; done|].
        exfalso.
        apply (irreflexivity lww_lt a).
        eapply transitivity; eauto.
      + assert (e = e') as ->; [inversion Heqe; done|].
        exfalso.
        apply (irreflexivity lww_lt a).
        eapply transitivity; eauto.
      + rewrite Heq Heq'; done.
  Qed.

  Lemma lww_max_singleton (ev : Event (LWWOp PT)) : lww_max ev {[ev]}.
  Proof.
    split; [set_solver|].
    intros e' ->%elem_of_singleton Hne.
    exfalso.
    by apply Hne.
  Qed.

  Lemma lww_max_singleton' (e e' : Event (LWWOp PT)) : lww_max e {[e']} -> e = e'.
  Proof.
    intros [->%elem_of_singleton _]; done.
  Qed.

  Hint Resolve lww_max_singleton : core.
  Hint Resolve events_ext_singleton : core.

  Instance op_lww_register_effect_coh : OpCrdtEffectCoh op_lww_register_effect.
  Proof.
    intros s ev st st' [[-> ->] | [e [Heq [_ Hlww]]]] Hnotin Hmax Hevs_ext Htot.
    - split.
      + intros [[_ ->] | [e [He _]]].
        * right; exists ev.
          assert (∅ ∪ {[ev]} = {[ev]}) as ->; [set_solver|].
          eauto.
        * exfalso; inversion He.
      + intros [[Heq _] | [e [Heq [Hext Hmax']]]].
        * exfalso; set_solver.
        * left.
          rewrite Heq.
          assert (∅ ∪ {[ev]} = ({[ev]} : gset (Event (LWWOp PT)))) as Hset.
          { set_solver. }
          rewrite Hset in Hmax'.
          apply lww_max_singleton' in Hmax' as ->.
          done.
    - split.
      + intros [[-> ->] | [e' [-> [[-> Hlt] | [-> Hlt]]]]].
        * exfalso.
          inversion Heq.
        * inversion Heq; subst.
          right.
          assert (lww_max e (s ∪ {[ev]})) as ?; [ | by eauto].
          destruct Hlww as [Hein Hemax].
          split; [set_solver|].
          intros e' [Hein' | ->%elem_of_singleton]%elem_of_union Hne; [|done].
          apply Hemax; done.
        * right.
          assert (lww_max ev (s ∪ {[ev]})) as ?; [ | by eauto].
          split; [set_solver|].
          intros e'' [Hein' | ->%elem_of_singleton]%elem_of_union Hne; [|done].
          inversion Heq; subst.
          destruct (decide (e'' = e)) as [-> | Hne']; [done|].
          destruct Hlww as [_ Hemax].
          apply Hemax in Hein'; [|done].
          eapply transitivity; eauto.
      + intros [[Hnone _] | Hsome]; [set_solver|].
        destruct Hsome as [e' (-> & Hext' & Hmax')].
        rewrite Heq.
        destruct Hmax' as [[Hein' | ->%elem_of_singleton]%elem_of_union Hmax'].
        * destruct (decide (e = e')) as [-> | Hne].
          ** right.
             exists e'. split; [done|].
             left; split; [done|].
             apply Hmax'; [set_solver|].
             intros ->.
             apply Hnotin; done.
          ** exfalso.
             apply (irreflexivity lww_lt e).
             destruct Hlww as [Hin Hlww].
             apply Hlww in Hein'; [|done].
             assert (e ∈ s ∪ {[ev]}) as Hein; [set_solver|].
             apply Hmax' in Hein; [|done].
             eapply transitivity; eauto.
        * right; exists e.
          split; [done|].
          right.
          destruct Hlww as [Hin Hlww].
          assert (e ∈ s ∪ {[ev]}) as Hein; [set_solver|].
          split; [done|].
          apply Hmax'; [set_solver|].
          intros ->.
          apply Hnotin; done.
  Qed.

  Definition op_lww_register_init_st : @LWWSt PT := None.

  Lemma op_lww_register_init_st_coh : ⟦ (∅ : gset (Event (LWWOp PT))) ⟧ ⇝ op_lww_register_init_st.
  Proof. by left. Qed.

  Global Instance op_lww_register_model_instance : OpCrdtModel (LWWOp PT) LWWSt := {
    op_crdtM_effect := op_lww_register_effect;
    op_crdtM_effect_fun := op_lww_register_effect_fun;
    op_crdtM_effect_coh := op_lww_register_effect_coh;
    op_crdtM_init_st := op_lww_register_init_st;
    op_crdtM_init_st_coh := op_lww_register_init_st_coh
  }.

End OpLWWRegister.


Section LWWreg_proof.
  Context `{PayloadT : Type}.
  Context `{!EqDecision PayloadT, !Countable PayloadT}.
  Context `{!Inject PayloadT val}.
  Context `{!∀ p : PayloadT, Serializable vl_serialization $ p}.
  Context `{!anerisG M Σ}.

  (* TODO: generalize the payload type *)
  Notation LWWOp' := (LWWOp PayloadT).
  Notation LWWSt' := (@LWWSt PayloadT).
  Notation Event' := (Event LWWOp').

  Context `{!CRDT_Params, !OpLib_Res LWWOp'}.

  Definition lww_register_OpLib_Op_Coh := λ (op : LWWOp') v, match op with Write z => v = $z end.

  Lemma lww_register_OpLib_Op_Coh_Inj (o1 o2 : LWWOp') (v : val) :
    lww_register_OpLib_Op_Coh o1 v → lww_register_OpLib_Op_Coh o2 v → o1 = o2.
  Proof. destruct o1; destruct o2; simpl; intros ? ?; simplify_eq; done. Qed.

  Lemma lww_register_OpLib_Coh_Ser (op : LWWOp') (v : val) :
    lww_register_OpLib_Op_Coh op v → Serializable vl_serialization v.
  Proof.
    destruct op; rewrite /lww_register_OpLib_Op_Coh; intros ?; simplify_eq; apply _.
  Qed.

  (* TODO: move to the right place. *)
  Global Instance vector_clock_inject : Inject vector_clock val :=
    { inject := vector_clock_to_val }.

  Definition lww_register_OpLib_State_Coh (st : LWWSt') (v : val) : Prop :=
    (v = NONEV ∧ st = None) ∨
    (∃ w ev, v = SOMEV w ∧
             st = Some ev ∧
             w = PairV (PairV $(lww_payload (EV_Op ev)) $(EV_Time ev)) #(EV_Orig ev)).

  Global Instance LWW_OpLib_Params : OpLib_Params LWWOp' LWWSt' :=
  {|
    OpLib_Serialization := vl_serialization;
    OpLib_State_Coh := lww_register_OpLib_State_Coh;
    OpLib_Op_Coh := lww_register_OpLib_Op_Coh;
    OpLib_Op_Coh_Inj := lww_register_OpLib_Op_Coh_Inj;
    OpLib_Coh_Ser := lww_register_OpLib_Coh_Ser
  |}.

  Lemma lww_register_init_st_fn_spec : ⊢ init_st_fn_spec lwwreg_init_st.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /lwwreg_init_st.
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    left; done.
  Qed.

  Lemma wp_vc_to_lamport addr vcv vc :
    {{{ ⌜is_vc vcv vc⌝ }}}
      vc_to_lamport vcv @[ip_of_address addr]
    {{{ l, RET #l; ⌜l = to_lamport vc⌝ }}}.
  Proof.
    generalize dependent vcv.
    induction vc as [ | h t IH]; iIntros (vcv Φ) "%Hvc HΦ"; rewrite /vc_to_lamport;
      inversion Hvc; subst.
    - wp_pures; iApply ("HΦ" $! 0); done.
    - match goal with
      | [ H : vcv = _ ∧ _ |- _ ] => destruct H as [-> Hislist]
      end.
      do 10 wp_pure _.
      wp_apply IH; [done|].
      iIntros (l) "%Htolamp"; wp_pures.
      assert ((Z.add (Z.of_nat h) (Z.of_nat l)) = Z.of_nat (h + l)) as -> by lia.
      iApply "HΦ"; iPureIntro.
      rewrite Htolamp; simpl; done.
  Qed.

  (* TODO: move to vector clock file *)
  Lemma wp_vect_eq vcv1 vcv2 vc1 vc2 addr :
    {{{ ⌜is_vc vcv1 vc1⌝ ∗ ⌜is_vc vcv2 vc2⌝ }}}
      vect_eq vcv1 vcv2 @[ip_of_address addr]
    {{{ (b : bool), RET #b; ⌜b = true <-> vc1 = vc2⌝}}}.
  Proof.
    iIntros (Φ) "[%Hvc1 %Hvc2] HΦ"; rewrite /vect_eq; wp_pures.
    wp_apply wp_vect_leq; [done|].
    iIntros (v) "->".
    destruct (bool_decide_reflect (vector_clock_le vc1 vc2)) as [Hle | Hne]; wp_pures.
    - wp_apply wp_vect_leq; [done|].
      iIntros (v') "->".
      destruct (bool_decide_reflect (vector_clock_le vc2 vc1)) as [Hle' | Hne'];
        wp_pures; iApply "HΦ"; iPureIntro; split; intros Heq; [| done | done | ].
      + apply (@anti_symm _ _ vector_clock_le); [apply _| done | done].
      + exfalso; apply Hne'; rewrite Heq; apply reflexivity.
    - iApply "HΦ"; iPureIntro; split; [done|];
        intros Heq; exfalso; apply Hne; rewrite Heq; apply reflexivity.
  Qed.

  Lemma wp_vect_lt vcv1 vcv2 vc1 vc2 addr :
    {{{ ⌜is_vc vcv1 vc1⌝ ∗ ⌜is_vc vcv2 vc2⌝ }}}
      vect_lt vcv1 vcv2 @[ip_of_address addr]
    {{{ (b : bool), RET #b; ⌜b = true <-> vector_clock_lt vc1 vc2⌝ }}}.
  Proof.
    iIntros (Φ) "[%Hvc1 %Hvc2] HΦ"; rewrite /vect_lt; wp_pures.
    wp_apply wp_vect_leq; [done |].
    iIntros (v) "->".
    destruct (bool_decide_reflect (vector_clock_le vc1 vc2)) as [Hle | Hne]; wp_pures.
    - wp_apply wp_vect_eq; [done|].
      iIntros (b) "%Hb".
      destruct b; wp_pures; iApply "HΦ"; iPureIntro; split; intros Harg.
      + inversion Harg.
      + pose proof ((iffLR Hb) eq_refl) as ->.
        apply vector_clock_lt_irreflexive in Harg; done.
      + apply vector_clock_le_eq_or_lt in Hle as [-> | Hne]; [ | done].
        exfalso; pose proof ((iffRL Hb) eq_refl) as ?; done.
      + done.
    - iApply "HΦ"; iPureIntro; split; [done| intros Hlt].
      exfalso; apply Hne; by apply vector_clock_lt_le.
  Qed.

  Definition is_ts (vc : vector_clock) (orig : nat) (v : val) :=
    ∃ vcv, v = PairV vcv #orig ∧ is_vc vcv vc.

  Definition ts_lt vc1 orig1 vc2 orig2 :=
    let l1 := to_lamport vc1 in
    let l2 := to_lamport vc2 in
    (l1 < l2) ∨ (l1 = l2 ∧ orig1 < orig2).

  Lemma ts_lt_lww_lt (ev1 ev2 : Event') :
    ts_lt (EV_Time ev1) (EV_Orig ev1) (EV_Time ev2) (EV_Orig ev2) -> lww_lt ev1 ev2.
  Proof.
    intros [Hlt1 | Hlt2]; [left | right]; done.
  Qed.

  Lemma wp_tstamp_lt vc1 orig1 vc2 orig2 tsv1 tsv2 addr :
    {{{ ⌜is_ts vc1 orig1 tsv1⌝ ∗ ⌜is_ts vc2 orig2 tsv2⌝ }}}
      tstamp_lt tsv1 tsv2 @[ip_of_address addr]
    {{{ b, RET #b; ⌜b = true <-> ts_lt vc1 orig1 vc2 orig2⌝ }}}.
  Proof.
    iIntros (Φ) "[%Hvc1 %Hvc2] HΦ"; rewrite /tstamp_lt; wp_pures.
    destruct Hvc1 as [vcv1 [-> Hvc1]]; destruct Hvc2 as [vcv2 [-> Hvc2]]; wp_pures.
    wp_apply wp_vc_to_lamport; [done |]; iIntros (l1) "%Hl1"; wp_pures.
    wp_apply wp_vc_to_lamport; [done |]; iIntros (l2) "%Hl2"; wp_pures.
    destruct (bool_decide_reflect (l1 < l2)%Z) as [Hle | Hnle]; wp_pures.
    - iApply "HΦ"; iPureIntro; split; [ | done].
      intros _; left; lia.
    - destruct (bool_decide_reflect (@eq Z l1 l2)%Z) as [Heq | Hne]; wp_pures.
      + destruct (bool_decide_reflect (orig1 < orig2)%Z) as [Hlo | Hnlo]; iApply "HΦ";
          iPureIntro.
        * split; [|done].
          intros _; right.
          rewrite <- Hl1, <- Hl2; auto with lia.
        * split; [done| intros [Hlt1 | [_ Hlt2]]]; lia.
      + iApply "HΦ"; iPureIntro; split; [done | intros [Hlt1 | Hlt2]]; lia.
  Qed.

  Lemma lww_register_effect_spec : ⊢ effect_spec lwwreg_effect.
  Proof.
    iIntros (addr ev st s log_ev log_st).
    iIntros "!#" (Φ) "(%Hev & %Hst & %Hs & %Hevs) HΦ".
    rewrite /lwwreg_effect.
    destruct log_ev as [[op] orig vc].
    destruct Hev as (evpl&evvc&evorig&?&Hevpl&Hisvc&?).
    destruct Hevs as (Hev & Hmax & Hext & Htot).
    simplify_eq/=.
    wp_pures.
    destruct Hst as [[-> ->] | Hsome].
    - wp_pures.
      iApply "HΦ".
      iPureIntro.
      set ev := (@Build_Event vc_time LWWOp' (Write op) orig vc).
      exists (Some ev).
      split.
      + right.
        eexists _, ev.
        split; [eauto|].
        apply is_vc_vector_clock_to_val in Hisvc.
        assert (time {| EV_Op := Write op; EV_Orig := orig; EV_Time := vc |} = vc) as Heq.
        { compute. done. }
        rewrite Heq in Hisvc.
        rewrite <- Hisvc.
        done.
      + by left.
    - destruct Hsome as [w [ev (-> & -> & ->)]].
      wp_pures.
      rewrite /assert.
      wp_apply wp_tstamp_lt; [iPureIntro|].
      { split; last first.
        + rewrite /is_ts; eexists; eauto.
        +  rewrite /is_ts; eexists; split; [eauto| eapply vector_clock_to_val_is_vc]. }
      iIntros (b) "%Hts".
      destruct b; wp_pures.
      + iApply "HΦ"; iPureIntro.
        set new_ev := (@Build_Event vc_time LWWOp' (Write op) orig vc).
        exists (Some new_ev).
        split.
        * right.
          exists (PairV (PairV $op evvc) #orig), new_ev.
          repeat split; try eauto.
          subst new_ev; simpl.
          apply is_vc_vector_clock_to_val in Hisvc.
          assert (time {| EV_Op := Write op; EV_Orig := orig; EV_Time := vc |} = vc) as Heq.
          { compute; done. }
          rewrite Heq in Hisvc; rewrite Hisvc; done.
        * right; exists ev; split; [done|]; right; split; [done|].
          apply ts_lt_lww_lt.
          apply Hts; done.
      + wp_apply wp_tstamp_lt; [iPureIntro|].
        { split; last first.
          +  rewrite /is_ts; eexists; split; [eauto| eapply vector_clock_to_val_is_vc].
          + rewrite /is_ts; eexists; eauto. }
        iIntros (b') "%Hts'".
        destruct b'; wp_pures.
        * iApply "HΦ".
          iPureIntro. exists (Some ev); split.
          ** right. exists (PairV (PairV $(lww_payload (EV_Op ev)) (vector_clock_to_val (EV_Time ev))) #(EV_Orig ev)).
             eauto.
          ** right. exists ev. split; [done|]. left. split; [done|].
             apply ts_lt_lww_lt.
             simpl in *.
             assert (time {| EV_Op := Write op; EV_Orig := orig; EV_Time := vc |} = vc) as Heq.
             { compute; done. }
             rewrite Heq in Hts'.
             by apply Hts'.
        * exfalso.
          assert (time {| EV_Op := Write op; EV_Orig := orig; EV_Time := vc |} = vc) as Heq.
          { compute; done. }
          rewrite Heq in Hts. rewrite Heq in Hts'.
          destruct (decide (to_lamport (EV_Time ev) < to_lamport vc)) as [Hlt | Hnlt].
          ** assert (ts_lt (EV_Time ev) (EV_Orig ev) vc orig) as Hcontra.
             { left; done. }
             apply Hts in Hcontra.
             inversion Hcontra.
          ** destruct (decide (to_lamport vc < to_lamport (EV_Time ev))) as [Hlt' | Hnlt'].
             { assert (ts_lt vc orig (EV_Time ev) (EV_Orig ev)) as Hcontra.
               { left; done. }
               apply Hts' in Hcontra.
               inversion Hcontra. }
             assert (to_lamport (EV_Time ev) = to_lamport vc) as Hleq by lia.
             destruct (decide (orig < (EV_Orig ev))) as [Holt | Honlt].
             { assert (ts_lt vc orig (EV_Time ev) (EV_Orig ev)) as Hcontra.
               { right; done. }
               apply Hts' in Hcontra.
               inversion Hcontra. }
             destruct (decide ((EV_Orig ev) < orig)) as [Holt' | Honlt'].
             { assert (ts_lt (EV_Time ev) (EV_Orig ev) vc orig ) as Hcontra.
               { right; done. }
               apply Hts in Hcontra.
               inversion Hcontra. }
             assert (orig = (EV_Orig ev)) as Hoeq by lia.
             set new_ev := (@Build_Event vc_time LWWOp' (Write op) orig vc).
             destruct Hs as [[_ Hnone] | [e [Heeq [_ [Hein Hemax]]]]]; [inversion Hnone; done|].
             simplify_eq /=.
             assert (e ∈ s ∪ {[{| EV_Op := Write op; EV_Orig := EV_Orig e; EV_Time := vc |}]}) as Hin1; [set_solver|].
             assert (new_ev ∈ s ∪ {[{| EV_Op := Write op; EV_Orig := EV_Orig e; EV_Time := vc |}]}) as Hin2; [set_solver|].
             assert (e ≠ new_ev) as Hne.
             { intros contra.
               apply Hev.
               subst new_ev. rewrite <- contra.
               done. }
             pose proof (Htot e new_ev Hin1 Hin2 Hne eq_refl) as
               [Hlt1%vector_clock_lt_to_lamport_lt | Hlt2%vector_clock_lt_to_lamport_lt].
             *** rewrite /time /Event_Timed in Hlt1; simpl in Hlt1; done.
             *** rewrite /time /Event_Timed in Hlt2; simpl in Hlt2; done.
  Qed.

  Lemma lww_register_crdt_fun_spec : ⊢ crdt_fun_spec lwwreg_crdt.
  Proof.
    iIntros (addr).
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /lwwreg_crdt.
    wp_pures.
    iApply "HΦ".
    iExists _, _; iSplit; first done.
    iSplit; [iApply lww_register_init_st_fn_spec|iApply lww_register_effect_spec].
  Qed.

  Lemma lww_init_spec :
    init_spec (oplib_init
               (s_ser (s_serializer OpLib_Serialization))
               (s_deser (s_serializer OpLib_Serialization))) -∗
    init_spec_for_specific_crdt 
    (lwwreg_init (s_ser (s_serializer vl_serialization)) (s_deser (s_serializer vl_serialization))).
  Proof.
    iIntros "#Hinit" (repId addr addrs_val).
    iIntros (Φ) "!# (%Haddrs & %Hrepid & Hprotos & Hskt & Hfr & Htoken) HΦ".
    rewrite /lwwreg_init.
    wp_pures.
    wp_apply ("Hinit" with "[$Hprotos $Htoken $Hskt $Hfr]").
    { do 2 (iSplit; first done). iApply lww_register_crdt_fun_spec; done. }
    iIntros (get update) "(HLS & #Hget & #Hupdate)".
    wp_pures.
    iApply "HΦ"; eauto.
  Qed.

End LWWreg_proof.
