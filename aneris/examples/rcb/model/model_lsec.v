(**  Mathematical model of the causal memory implementation
     from "Causal memory: definitions, implementation, and programming"
     (https://link.springer.com/article/10.1007/BF01784241).*)

From aneris.aneris_lang Require Import resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Export events.

(** Local history validity. *)
Section Local_history_section_valid.
  Context `{!anerisG Mdl Σ, !RCB_params}.

  Definition RCBM_lsec (j : nat) (s : gset local_event) : gset local_event :=
    filter (λ x, x.(le_orig) = j) s.

  Definition RCBM_lsec_complete (j : nat) (s : gset local_event) :=
    ∀ k, (1 ≤ k ∧ k <= length (elements (RCBM_lsec j s))) →
         ∃ a, a ∈ (RCBM_lsec j s) ∧ a.(le_time) !! j = Some k.

  Definition RCBM_lsec_latest_in_frame
             (j' : nat) (s : gset local_event) (x : local_event) :=
    nat_sup
      (omap
         (λ e, e.(le_time) !! j')
         (filter
            (λ e, e.(le_seqid) < x.(le_seqid))
            (elements (RCBM_lsec j' s)))).

  Definition  RCBM_lsec_locally_causal_refl (i : nat) (s : gset local_event) :=
    ∀ j' x,
      j' < length RCB_addresses →
      j' ≠ i →
      x ∈ RCBM_lsec i s →
      (x.(le_time) !! j' = Some (RCBM_lsec_latest_in_frame j' s x)).

  Definition RCBM_lsec_locally_causal (j : nat) (s : gset local_event) :=
    ∀ j' x,
      j' < length RCB_addresses →
      j' ≠ j →
      x ∈ RCBM_lsec j s →
      from_option
        (λ a, a ≤ RCBM_lsec_latest_in_frame j' s x) False (x.(le_time) !! j').

  Record RCBM_lsec_valid (i j: nat) (s : gset local_event) : Prop := {
    RCBM_LSV_bound_at: i < length RCB_addresses;
    RCBM_LSV_bound_orig: j < length RCB_addresses;
    RCBM_LSV_comp: RCBM_lsec_complete j s;
    RCBM_LSV_caus_refl: RCBM_lsec_locally_causal_refl i s;
    RCBM_LSV_caus: RCBM_lsec_locally_causal j s; }.

  Global Arguments RCBM_LSV_bound_at {_ _ _} _.
  Global Arguments RCBM_LSV_bound_orig {_ _ _} _.
  Global Arguments RCBM_LSV_comp {_ _ _} _.
  Global Arguments RCBM_LSV_caus_refl {_ _ _} _.
  Global Arguments RCBM_LSV_caus {_ _ _} _.

  Definition RCBM_lsec_ext (j : nat) (s : gset local_event) :=
    ∀ x y, x ∈ RCBM_lsec j s → y ∈ RCBM_lsec j s →
           x.(le_time) !! j = y.(le_time) !! j → x = y.

  Definition RCBM_lsec_strongly_complete (j : nat) (s : gset local_event) :=
    ∀ k, (1 ≤ k ∧ k <= length (elements (RCBM_lsec j s))) ↔
         ∃ a, a ∈ (RCBM_lsec j s) ∧ a.(le_time) !! j = Some k.

  Lemma complete_list_of_nat_permutation_seq (l : list nat):
  (∀ k, (1 ≤ k ∧ k ≤ length l) → k ∈ l) → l ≡ₚ seq 1 (length l).
  Proof.
    intros Hl.
    symmetry.
    apply submseteq_length_Permutation.
    2: { by rewrite seq_length. }
    apply NoDup_submseteq; first by apply NoDup_ListNoDup, seq_NoDup.
    intros x Hx.
    apply Hl.
    setoid_rewrite elem_of_list_In in Hx.
    apply in_seq in Hx; lia.
  Qed.

  Lemma RCBM_lsec_complete_RCBM_lsec_times_j_NoDup j s :
    (∀ e, e ∈ s → length e.(le_time) = length RCB_addresses) →
    j < length RCB_addresses →
    RCBM_lsec_complete j s →
    ∃ l, map (λ e, e.(le_time) !! j) (elements (RCBM_lsec j s)) = map Some l ∧
         l ≡ₚ seq 1 (length l).
  Proof.
    intros Hl Hj Hcmp.
    exists (map (λ e : local_event, default 0 (le_time e !! j))
           (elements (RCBM_lsec j s))).
    split.
    - apply list_eq; intros i.
      rewrite !list_lookup_fmap /=.
      destruct (elements (RCBM_lsec j s) !! i) as [e|] eqn:Heq; simpl; last done.
      destruct (lookup_lt_is_Some_2 (le_time e) j) as [x Hx];
        last by rewrite Hx.
      rewrite Hl; first done.
      apply elem_of_list_lookup_2, elem_of_elements in Heq.
      apply elem_of_filter in Heq as [? ?]; done.
    - apply complete_list_of_nat_permutation_seq.
      rewrite map_length.
      intros k; specialize (Hcmp k).
      intros (e & He1 & He2)%Hcmp.
      apply elem_of_elements in He1.
      apply elem_of_list_lookup_1 in He1 as [i He1].
      apply elem_of_list_lookup.
      exists i; rewrite list_lookup_fmap He1 /= He2; done.
  Qed.

  Lemma RCBM_lsec_complete_RCBM_lsec_ext j s :
    (∀ e, e ∈ s → length e.(le_time) = length RCB_addresses) →
    j < length RCB_addresses →
    RCBM_lsec_complete j s → RCBM_lsec_ext j s.
  Proof.
    intros Htm Hj Hcmpl.
    destruct (RCBM_lsec_complete_RCBM_lsec_times_j_NoDup j s)
      as (l & Hleq & Hlperm); [done|done|done|].
    intros x y Hx%elem_of_elements Hy%elem_of_elements Heq.
    apply elem_of_list_lookup_1 in Hx as [i Hx].
    apply elem_of_list_lookup_1 in Hy as [i' Hy].
    assert (∃ n, l !! i = Some n ∧ l !! i' = Some n) as (n & Hn1 & Hn2).
    { pose proof (f_equal (λ u, u !! i) Hleq) as Hleqi; simpl in *.
      pose proof (f_equal (λ u, u !! i') Hleq) as Hleqi'; simpl in *.
      rewrite !list_lookup_fmap ?Hx ?Hy /= in Hleqi, Hleqi'.
      rewrite Heq in Hleqi.
      destruct (l !! i); destruct (l !! i');
        simpl in *; simplify_eq; eauto. }
    assert (i = i'); last by simplify_eq.
    eapply NoDup_lookup; [|done|done].
    rewrite Hlperm.
    apply NoDup_ListNoDup, seq_NoDup.
  Qed.

  Lemma RCBM_LSV_ext {i j s} :
    (∀ e, e ∈ s → length e.(le_time) = length RCB_addresses) →
    j < length RCB_addresses →
    RCBM_lsec_valid i j s →
    RCBM_lsec_ext j s.
  Proof.
    intros; apply RCBM_lsec_complete_RCBM_lsec_ext; eauto using RCBM_LSV_comp.
  Qed.

  Lemma RCBM_lsec_complete_RCBM_lsec_strongly_complete j s :
    (∀ e, e ∈ s → length e.(le_time) = length RCB_addresses) →
    j < length RCB_addresses →
    RCBM_lsec_complete j s → RCBM_lsec_strongly_complete j s.
  Proof.
    intros Htm Hj Hcmp.
    destruct (RCBM_lsec_complete_RCBM_lsec_times_j_NoDup j s)
      as (l & Hleq & Hlperm); [done|done|done|].
    intros k; split; first by apply Hcmp.
    intros (e & He1 & He2).
    rewrite -(map_length (λ e, le_time e !! j)) Hleq map_length.
    assert (In k (seq 1 (length l))) as ?%in_seq; last lia.
    rewrite -Hlperm.
    apply elem_of_elements, elem_of_list_lookup_1 in He1 as [i He1].
    pose proof (f_equal (λ l, l !! i) Hleq) as Hleqi; simpl in *.
    rewrite !list_lookup_fmap He1 /= He2 in Hleqi.
    destruct (l !! i) eqn:Heq; last done; simplify_eq/=.
    apply elem_of_list_In, elem_of_list_lookup; eauto.
  Qed.

  Lemma RCBM_LSV_strongly_complete {i j s} :
    (∀ e, e ∈ s → length e.(le_time) = length RCB_addresses) →
    j < length RCB_addresses →
    RCBM_lsec_valid i j s →
    RCBM_lsec_strongly_complete j s.
  Proof.
    intros; apply RCBM_lsec_complete_RCBM_lsec_strongly_complete;
      eauto using RCBM_LSV_comp.
  Qed.

  Lemma RCBM_lsec_of_empty j : RCBM_lsec j ∅ = ∅.
  Proof. by rewrite /RCBM_lsec filter_empty_L. Qed.

  Lemma in_lsec_orig e s : e ∈ s → e ∈ RCBM_lsec e.(le_orig) s.
  Proof. by rewrite /RCBM_lsec elem_of_filter. Qed.

  Lemma orig_in_lsec e j s : e ∈ RCBM_lsec j s → le_orig e = j.
  Proof. by rewrite /RCBM_lsec elem_of_filter; intros [? ?]. Qed.

  Lemma in_lsec_in_lhst e j s : e ∈ RCBM_lsec j s → e ∈ s.
  Proof. by rewrite /RCBM_lsec elem_of_filter; intros [? ?]. Qed.

  Lemma RCBM_lsec_latest_in_frame_empty j s x :
    RCBM_lsec j s = ∅ → RCBM_lsec_latest_in_frame j s x = 0.
  Proof.
    intros Hsec.
    apply Nat.le_0_r.
    rewrite /RCBM_lsec_latest_in_frame.
    apply nat_sup_LUB.
    intros a.
    rewrite Hsec elements_empty filter_nil /=; inversion 1.
  Qed.

  Lemma sections_empty_valid i j :
    i < length RCB_addresses →
    j < length RCB_addresses →
    RCBM_lsec_valid i j (RCBM_lsec j ∅).
  Proof.
    split; [done|done| |done|done].
    intros ?.
    rewrite /RCBM_lsec filter_empty_L elements_empty; simpl; lia.
  Qed.

  Lemma RCBM_lsec_union j s s' :
    RCBM_lsec j (s ∪ s') = RCBM_lsec j s ∪ RCBM_lsec j s'.
  Proof.
    apply set_eq; intros e.
    rewrite /RCBM_lsec elem_of_union !elem_of_filter; set_solver.
  Qed.

  Lemma RCBM_lsec_singleton_in j e :
    le_orig e = j → RCBM_lsec j {[e]} = {[e]}.
  Proof.
    intros ?; apply set_eq; intros e'.
    rewrite /RCBM_lsec !elem_of_filter; set_solver.
  Qed.

  Lemma RCBM_lsec_singleton_out j e :
    le_orig e ≠ j → RCBM_lsec j {[e]} = ∅.
  Proof.
    intros ?; apply set_eq; intros e'.
    rewrite /RCBM_lsec !elem_of_filter; set_solver.
  Qed.

End Local_history_section_valid.

