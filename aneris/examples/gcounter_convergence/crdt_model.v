From Coq.ssr Require Export ssreflect.
From stdpp Require Import base vector.
From aneris.examples.gcounter_convergence Require Import vc.
From trillium.traces Require Import infinite_trace trace trace_properties.
From aneris.prelude Require Import list.

Import InfListNotations.

Notation crdt_state n := (vec (vector_clock n) n).

Section crdt_model.

  Inductive CrdtNext {n} : crdt_state n → () -> crdt_state n → Prop :=
  | IncrStep st i : CrdtNext st tt (vinsert i (vc_incr i (st !!! i)) st)
  | ApplyStep st vc i j :
      vc_le vc (st !!! j) →
      CrdtNext st tt (vinsert i (vc_merge (st !!! i) vc) st).

  Definition initial_crdt_state (n : nat) : crdt_state n :=
    vreplicate n (vreplicate n 0).

  Definition valid_crdt_state {n :nat} (st : crdt_state n) : Prop :=
    ∀ i j, (st !!! j) !!! i ≤ (st !!! i) !!! i.

  Definition crtd_state_has_converged_to
             {n : nat} (vc : vector_clock n) (st : crdt_state n) : Prop := ∀ i, st !!! i = vc.

  Definition diagonal_of_crdt_state {n} (st : crdt_state n) (vc : vector_clock n) : Prop :=
    ∀ i, (st !!! i) !!! i = vc !!! i.


  Definition crdt_states_have_same_diagonal {n : nat} (s1 s2 : crdt_state n) : Prop :=
    (∀ i, (s1 !!! i) !!! i = (s2 !!! i) !!! i).

  (* Properties *)

  Lemma valid_initial_crdt_state n : valid_crdt_state (initial_crdt_state n).
  Proof. intros i j; rewrite /initial_crdt_state !vlookup_replicate; done. Qed.

  Lemma CrdtNext_preserves_validity n (s1 s2 : crdt_state n) :
    valid_crdt_state s1 → CrdtNext s1 tt s2 → valid_crdt_state s2.
  Proof.
    intros Hv1 Hss.
    inversion Hss as [? i|? vc i j Hle]; simplify_eq.
    - intros k l.
      destruct (decide (k = i)) as [->|].
      + rewrite !vlookup_insert.
        destruct (decide (l = i)) as [->|].
        * rewrite !vlookup_insert; done.
        * rewrite (vlookup_insert_ne i l) //; auto.
      + destruct (decide (l = i)) as [->|].
        * rewrite !vlookup_insert.
          rewrite !vlookup_insert_ne; auto.
        * rewrite !vlookup_insert_ne; auto.
    - intros k l.
      destruct (decide (k = i)) as [->|].
      + rewrite !vlookup_insert.
        destruct (decide (l = i)) as [->|].
        * rewrite !vlookup_insert; done.
        * rewrite (vlookup_insert_ne i l); last by auto.
          rewrite /vc_merge vlookup_zip_with.
          etrans; last apply Nat.le_max_l; auto.
      + destruct (decide (l = i)) as [->|].
        * rewrite !vlookup_insert.
          rewrite !vlookup_insert_ne; last by auto.
          rewrite /vc_merge vlookup_zip_with.
          apply Nat.max_lub; first done.
          etrans; first by apply Hle.
          done.
        * rewrite !vlookup_insert_ne; auto.
  Qed.

  Lemma crdt_state_has_converged_to_preserved n (vc : vector_clock n) (s1 s2 : crdt_state n) :
    crdt_states_have_same_diagonal s1 s2 →
    CrdtNext s1 tt s2 →
    crtd_state_has_converged_to vc s1 →
    crtd_state_has_converged_to vc s2.
  Proof.
    intros Hdiag Hstep Hhc.
    inversion Hstep as [? i|? vc' i j Hle]; simplify_eq.
    - exfalso.
      specialize (Hdiag i).
      revert Hdiag.
      rewrite !vlookup_insert; lia.
    - intros k.
      rewrite (Hhc i).
      rewrite (Hhc j) in Hle.
      rewrite [vc_merge _ _]comm_L vc_merge_vc_le //.
      destruct (decide (k = i)) as [->|].
      + rewrite vlookup_insert; done.
      + rewrite vlookup_insert_ne; auto.
  Qed.

  Lemma diagonal_of_crdt_state_agree n (s1 s2 : crdt_state n) (vc : vector_clock n) :
    diagonal_of_crdt_state s1 vc →
    diagonal_of_crdt_state s2 vc →
    crdt_states_have_same_diagonal s1 s2.
  Proof. intros Hs1 Hs2 i; rewrite (Hs1 i) (Hs2 i) //. Qed.

  Lemma crtd_state_has_converged_to_has_diagonal n (vc : vector_clock n) (s : crdt_state n) :
    crtd_state_has_converged_to vc s → diagonal_of_crdt_state s vc.
  Proof. intros Hsvc i; rewrite (Hsvc i) //. Qed.

  Lemma crdt_next_vc_le n (s1 s2 : crdt_state n) :
    CrdtNext s1 tt s2 → ∀ i, vc_le (s1 !!! i) (s2 !!! i).
  Proof.
    inversion 1; intros k l; simplify_eq.
    - destruct (decide (i = k)) as [->|].
      + rewrite vlookup_insert.
        destruct (decide (l = k)) as [->|].
        * rewrite vlookup_insert; eauto.
        * rewrite vlookup_insert_ne; auto.
      + rewrite vlookup_insert_ne; auto.
    - destruct (decide (i = k)) as [->|].
      + rewrite vlookup_insert.
        apply vc_merge_le1.
      + rewrite vlookup_insert_ne //.
  Qed.

  Lemma crdt_next_bounded n (s1 s2 : crdt_state n) :
    CrdtNext s1 tt s2 → ∀ i, vc_le (s2 !!! i) (vmap S (max_vc s1)).
  Proof.
    inversion 1 as [|???? Hle]; intros k l; simplify_eq.
    - rewrite vlookup_map.
      destruct (decide (i = k)) as [->|].
      + rewrite vlookup_insert.
        destruct (decide (l = k)) as [->|].
        * rewrite vlookup_insert.
          eapply le_n_S.
          apply max_vc_le.
        * rewrite vlookup_insert_ne; last by auto.
          etrans; first apply max_vc_le; lia.
      + rewrite vlookup_insert_ne; last done.
        etrans; first apply max_vc_le; lia.
    - destruct (decide (i = k)) as [->|].
      + rewrite vlookup_insert.
        apply vc_merge_lub.
        * etrans; first apply max_vc_le.
          intros ?; rewrite vlookup_map; lia.
        * etrans; first apply Hle.
          etrans; first apply max_vc_le.
          intros ?; rewrite vlookup_map; lia.
      + rewrite vlookup_insert_ne //.
        etrans; first apply max_vc_le.
        rewrite vlookup_map; lia.
  Qed.

  Fixpoint all_crdt_states_smaller m {n} (v : vector_clock n) : list (vec (vector_clock n) m) :=
    match m with
    | O => [[#]]
    | S m' =>
      flatten
        ((λ vcs, (λ vc, vc ::: vcs) <$> all_vecs_smaller v) <$> (all_crdt_states_smaller m' v))
    end.

  Lemma elem_of_all_crdt_states_smaller m n (v : vector_clock n) vcs:
    vcs ∈ all_crdt_states_smaller m v ↔ ∀ i, vc_le (vcs !!! i) v.
  Proof.
    revert vcs.
    induction m as [|m IHm]; simpl; intros vcs.
    { split.
      - intros ? i; inversion i.
      - intros _.
        apply (Vector.case0 (λ v', v' ∈ [[# ]])).
        apply elem_of_list_singleton; done. }
    rewrite elem_of_flatten.
    setoid_rewrite elem_of_list_fmap.
    split.
    - intros (l'' & Hvcs & vc & -> & Hvc) i.
      inv_all_vec_fin; simpl in *.
      + apply elem_of_list_fmap in Hvcs as (vc' & Heq & Hvc').
        simplify_eq.
        apply elem_of_all_vecs_smaller; done.
      + apply elem_of_list_fmap in Hvcs as (vc' & Heq & Hvc').
        simplify_eq.
        apply IHm; done.
    - intros Hle.
      inv_all_vec_fin.
      eexists _; split; last first.
      + eexists _; split; first reflexivity.
        apply IHm.
        intros i.
        apply (Hle (Fin.FS i)).
      + apply elem_of_list_fmap.
        eexists _; split; first done.
        apply elem_of_all_vecs_smaller.
        apply (Hle 0%fin).
  Qed.

End crdt_model.

Section crdt_model_prop.
  Context {n : nat}.

  Notation crdt_state := (crdt_state n).
  Notation vector_clock := (vector_clock n).

  Notation crdt_fintr := (finite_trace crdt_state ()).
  Notation crdt_inftr := (inflist (() * crdt_state)).
  Notation eventually := (@eventually crdt_state).
  Notation always := (@always crdt_state).

  Definition model_trace_makes_steps (f : crdt_fintr) (inftr : crdt_inftr) : Prop :=
    always (λ f' _, trace_steps CrdtNext f') f inftr.

  Definition valid_model_trace (f :crdt_fintr) (inftr : crdt_inftr) : Prop :=
    always (λ f' _, trace_forall (@valid_crdt_state n) f' ∧
                    trace_steps (λ st _ st', st = st' ∨ CrdtNext st tt st') f') f inftr.

  Lemma model_trace_makes_steps_valid_model_trace f inftr :
    model_trace_makes_steps f inftr → valid_crdt_state (trace_first f) →
    valid_model_trace f inftr.
  Proof.
    intros Hsteps Hvl.
    assert (always (λ f' _, valid_crdt_state (trace_first f')) f inftr) as Hvl'.
    { apply always_take_drop; intros k; rewrite trace_append_list_first; done. }
    assert (always (λ f' _, valid_crdt_state (trace_first f') ∧ trace_steps CrdtNext f') f inftr)
      as Hand.
    { by apply always_and. }
    clear Hsteps Hvl Hvl'.
    revert Hand; apply always_mono.
    clear f inftr. intros f _ [Hvi Hsteps].
    induction Hsteps as [|?? [] ? <- ? _ IH]; first by split; constructor; eauto.
    destruct IH as [IH1 IH2]; first done.
    split; last by econstructor; eauto.
    constructor; first by apply IH1.
    eapply CrdtNext_preserves_validity; last by auto.
    apply trace_forall_last; done.
  Qed.

  Definition stability_point_is_reached
             (vc : vector_clock) (f :crdt_fintr) (inftr : crdt_inftr) : Prop :=
   always (λ f' _, diagonal_of_crdt_state (trace_last f') vc) f inftr.

  Definition has_converged_to
             (vc : vector_clock) (f : crdt_fintr) (inftr : crdt_inftr) : Prop :=
    crtd_state_has_converged_to vc (trace_last f).

  Definition convergence_point_is_reached
             (vc : vector_clock) (f : crdt_fintr) (inftr : crdt_inftr) : Prop :=
    always (has_converged_to vc) f inftr.

  Lemma valid_trace_remains_converged_after_stability vc f inftr :
    valid_model_trace f inftr →
    stability_point_is_reached vc f inftr →
    has_converged_to vc f inftr →
    convergence_point_is_reached vc f inftr.
  Proof.
    revert f inftr; cofix IH; intros f inftr Hvl Hstb Hhc.
    constructor; first done.
    intros [] a ? ->.
    apply IH; [by apply always_unroll|by apply always_unroll|].
    rewrite /has_converged_to.
    assert (diagonal_of_crdt_state (trace_last (f :tr[()]: a)) vc).
    { by apply always_unroll, always_holds in Hstb. }
    destruct (decide (trace_last f = a)) as [<-|]; first done.
    eapply (crdt_state_has_converged_to_preserved _ _ (trace_last f)).
    - eapply diagonal_of_crdt_state_agree; last done.
      apply crtd_state_has_converged_to_has_diagonal; done.
    - apply always_unroll, always_holds in Hvl as [? [? (?&<-&[|])]%trace_steps_step_inv]; done.
    - done.
  Qed.

  Definition will_be_merged_ij (i j : fin n) (f : crdt_fintr) (inftr : crdt_inftr) : Prop :=
    eventually (λ f' _, vc_le ((trace_last f) !!! i) ((trace_last f') !!! j)) f inftr.

  Definition fair_model_trace_ij (i j : fin n) (f : crdt_fintr) (inftr : crdt_inftr) : Prop :=
    always (λ f' inftr', will_be_merged_ij i j f' inftr') f inftr.

  Definition fair_model_trace (f : crdt_fintr) (inftr : crdt_inftr) : Prop :=
    ∀ i j, fair_model_trace_ij i j f inftr.

  Definition has_caught_up_with_for_ij
             (i j : fin n) (vc : vector_clock) (f : crdt_fintr) (inftr : crdt_inftr) : Prop :=
    ((trace_last f) !!! j) !!! i = vc !!! i.

  Definition has_caught_up_with_for_ij_strong
             (i j : fin n) (vc : vector_clock) (f : crdt_fintr) (inftr : crdt_inftr) : Prop :=
    always (has_caught_up_with_for_ij i j vc) f inftr.

  Lemma all_caught_up_crdt_state_has_converged_to vc f inftr :
    valid_model_trace f inftr →
    stability_point_is_reached vc f inftr →
    (∀ i j, has_caught_up_with_for_ij_strong i j vc f inftr) →
    convergence_point_is_reached vc f inftr.
  Proof.
    intros Hvl Hstb Hacu.
    eapply valid_trace_remains_converged_after_stability; [done|done|].
    intros i; apply vec_eq; intros j.
    specialize (Hacu j i); apply always_holds in Hacu.
    apply Hacu.
  Qed.

  Lemma has_caught_up_with_for_ij_iff_strong i j vc f inftr :
    valid_model_trace f inftr →
    stability_point_is_reached vc f inftr →
    has_caught_up_with_for_ij i j vc f inftr ↔
    has_caught_up_with_for_ij_strong i j vc f inftr.
  Proof.
    intros Hvl Hstab.
    split; last first.
    { intros ?%always_holds; done. }
    revert f inftr Hvl Hstab.
    cofix IH; intros f inftr Hvl Hstab Hhcu.
    constructor; first done.
    intros [] a ? ->.
    apply always_unroll in Hstab.
    apply always_unroll in Hvl.
    apply IH; [done|done|].
    apply always_holds in Hstab.
    apply always_holds in Hvl as [Hvl Hsteps].
    apply Nat.le_antisymm; simpl.
    - apply trace_forall_extend_inv in Hvl as [Hvl1 Hvl2].
      etrans; first apply (Hvl2 i j).
      rewrite /= in Hstab; rewrite Hstab //.
    - apply trace_steps_step_inv in Hsteps as [Hsteps1 (b & <- & [<-|Hb2])].
      + rewrite Hhcu; done.
      + etrans; last by apply crdt_next_vc_le.
        rewrite Hhcu; done.
  Qed.

  Lemma has_reached_stability_point_fair_model_eventually_catches_up_for_ij
        (i j : fin n) (vc : vector_clock) (f : crdt_fintr) (inftr : crdt_inftr) :
    valid_model_trace f inftr →
    fair_model_trace_ij i j f inftr →
    stability_point_is_reached vc f inftr →
    eventually (has_caught_up_with_for_ij_strong i j vc) f inftr.
  Proof.
    intros Hvl Hfr Hstab.
    apply always_holds in Hfr.
    assert (diagonal_of_crdt_state (trace_last f) vc) as Hdiagf.
    { apply always_holds in Hstab; done. }
    pose proof (conj Hvl Hstab) as Hvlstb; apply always_and in Hvlstb.
    eapply eventually_and_always in Hvlstb; last apply Hfr.
    revert Hvlstb; apply eventually_mono.
    simpl; clear -Hdiagf.
    intros f' inftr' [Hle Hvl].
    apply has_caught_up_with_for_ij_iff_strong.
    { eapply always_mono; last by apply Hvl. simpl; tauto. }
    { eapply always_mono; last by apply Hvl. simpl; tauto. }
    apply always_holds in Hvl as [[Hvl Hsteps] Hstab].
    rewrite /has_caught_up_with_for_ij.
    rewrite -(Hstab i).
    apply Nat.le_antisymm.
    - apply trace_forall_last in Hvl. apply Hvl.
    - etrans; last apply Hle.
      rewrite (Hstab i) (Hdiagf i); done.
  Qed.

  Lemma has_reached_stability_point_fair_model_eventually_catches_up
        (vc : vector_clock) (f : crdt_fintr) (inftr : crdt_inftr) :
    valid_model_trace f inftr →
    (∀ i j, fair_model_trace_ij i j f inftr) →
    stability_point_is_reached vc f inftr →
    eventually
      (λ f' inftr',
       valid_model_trace f' inftr' ∧
       (∀ i j, fair_model_trace_ij i j f' inftr') ∧
       stability_point_is_reached vc f' inftr' ∧
       (∀ i j, has_caught_up_with_for_ij_strong i j vc f' inftr')) f inftr.
  Proof .
    intros Hvl Hfr Hstab.
    cut
      (eventually
         (λ (f' : crdt_fintr) (inftr' : crdt_inftr),
          (always (λ f'' inftr'', (trace_forall valid_crdt_state f'' ∧
                                   trace_steps (λ st _ st', st = st' ∨ CrdtNext st tt st') f'') ∧
                                  (∀ i j, will_be_merged_ij i j f'' inftr'') ∧
                                  (diagonal_of_crdt_state (trace_last f'') vc)) f' inftr') ∧
          (always (λ f'' inftr'', ∀ i j, has_caught_up_with_for_ij i j vc f'' inftr'') f' inftr')) f
         inftr).
    { apply eventually_mono.
      simpl; clear.
      intros f' inftr' [Hal1 Hal2].
      split_and!.
      - eapply always_mono; last by apply Hal1.
        simpl; tauto.
      - intros i j; eapply always_mono; last by apply Hal1.
        simpl; by firstorder.
      - eapply always_mono; last by apply Hal1.
        simpl; tauto.
      - intros i j; eapply always_mono; last by apply Hal2.
        simpl; by firstorder. }
    apply eventually_always_combine.
    { apply holds_eventually.
      apply always_and; split; first by auto.
      apply always_and; split; last by auto.
      rewrite -always_forall; intros i.
      rewrite -always_forall; intros j.
      apply Hfr. }
    cut (eventually
           (λ f' inftr', ∀ ij, has_caught_up_with_for_ij_strong ij.1 ij.2 vc f' inftr') f inftr).
    { apply eventually_mono.
      clear. intros f inftr Hij.
      rewrite -always_forall; intros i.
      rewrite -always_forall; intros j.
      apply (Hij (i, j)). }
    apply eventually_forall_combine.
    intros [i j]; simpl.
    apply has_reached_stability_point_fair_model_eventually_catches_up_for_ij; auto.
  Qed.

  Theorem eventually_consistent (vc : vector_clock) (f : crdt_fintr) (inftr : crdt_inftr) :
    eventually valid_model_trace f inftr →
    eventually fair_model_trace f inftr →
    eventually (stability_point_is_reached vc) f inftr →
    eventually (convergence_point_is_reached vc) f inftr.
  Proof.
    intros Hvl Hfm Hstab.
    assert (eventually
              (λ f' inftr',
               valid_model_trace f' inftr' ∧
               (∀ i j, fair_model_trace_ij i j f' inftr') ∧
               stability_point_is_reached vc f' inftr') f inftr) as
    Hev.
    { eapply eventually_mono; last first.
      - apply eventually_always_combine; first apply Hstab.
        eapply (eventually_mono (λ f' inftr', always _ f' inftr' ∧ always _ f' inftr'));
          first by intros ? ?; apply always_and.
        apply eventually_always_combine; [apply Hvl|].
        eapply eventually_mono; last by apply Hfm.
        rewrite /fair_model_trace.
        intros ? ?; do 2 setoid_rewrite always_forall; eauto.
      - simpl; clear.
        intros f' inftr' [Hstab Hal].
        split.
        { eapply always_mono;last by apply Hal. simpl; tauto. }
        split; last done.
        setoid_rewrite always_forall; rewrite always_forall.
        eapply always_mono; last by apply Hal.
        simpl; tauto. }
    clear -Hev.
    assert (eventually
              (λ f' inftr',
               valid_model_trace f' inftr' ∧
               (∀ i j, fair_model_trace_ij i j f' inftr') ∧
               stability_point_is_reached vc f' inftr' ∧
               (∀ i j, has_caught_up_with_for_ij_strong i j vc f' inftr')) f inftr) as Hev'.
    { apply eventually_idemp.
      eapply eventually_mono; last by apply Hev.
      clear; simpl.
      intros f inftr (Hvl & Hfr & Hstab).
      apply has_reached_stability_point_fair_model_eventually_catches_up; auto. }
    clear Hev.
    eapply eventually_mono; last by apply Hev'.
    simpl; clear.
    intros f inftr (Hvl & Hfr & Hstab & Hcu).
    apply all_caught_up_crdt_state_has_converged_to; auto.
  Qed.

End crdt_model_prop.
