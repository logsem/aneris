(**  Mathematical model of the causal memory implementation
     from "Causal memory: definitions, implementation, and programming"
     (https://link.springer.com/article/10.1007/BF01784241).*)

From aneris.aneris_lang Require Import resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Export events.

(** Local history validity. *)
Section Local_history_section_valid.
  Context `{!anerisG Mdl Σ, !DB_params}.

  Definition DBM_lsec (j : nat) (s : gset apply_event) : gset apply_event :=
    filter (λ x, x.(ae_orig) = j) s.

  Definition DBM_lsec_complete (j : nat) (s : gset apply_event) :=
    ∀ k, (1 ≤ k ∧ k <= length (elements (DBM_lsec j s))) →
         ∃ a, a ∈ (DBM_lsec j s) ∧ a.(ae_time) !! j = Some k.

  Definition DBM_lsec_latest_in_frame
             (j' : nat) (s : gset apply_event) (x : apply_event) :=
    nat_sup
      (omap
         (λ e, e.(ae_time) !! j')
         (filter
            (λ e, e.(ae_seqid) < x.(ae_seqid))
            (elements (DBM_lsec j' s)))).

  Definition DBM_lsec_locally_causal_refl (i : nat) (s : gset apply_event) :=
    ∀ j' x,
      j' < length DB_addresses →
      j' ≠ i →
      x ∈ DBM_lsec i s →
      (x.(ae_time) !! j' = Some (DBM_lsec_latest_in_frame j' s x)).

  Definition DBM_lsec_locally_causal (j : nat) (s : gset apply_event) :=
    ∀ j' x,
      j' < length DB_addresses →
      j' ≠ j →
      x ∈ DBM_lsec j s →
      from_option
        (λ a, a ≤ DBM_lsec_latest_in_frame j' s x) False (x.(ae_time) !! j').

  Record DBM_lsec_valid (i j: nat) (s : gset apply_event) : Prop := {
    DBM_LSV_bound_at: i < length DB_addresses;
    DBM_LSV_bound_orig: j < length DB_addresses;
    DBM_LSV_comp: DBM_lsec_complete j s;
    DBM_LSV_caus_refl: DBM_lsec_locally_causal_refl i s;
    DBM_LSV_caus: DBM_lsec_locally_causal j s; }.

  Global Arguments DBM_LSV_bound_at {_ _ _} _.
  Global Arguments DBM_LSV_bound_orig {_ _ _} _.
  Global Arguments DBM_LSV_comp {_ _ _} _.
  Global Arguments DBM_LSV_caus_refl {_ _ _} _.
  Global Arguments DBM_LSV_caus {_ _ _} _.

  Definition DBM_lsec_ext (j : nat) (s : gset apply_event) :=
    ∀ x y, x ∈ DBM_lsec j s → y ∈ DBM_lsec j s →
           x.(ae_time) !! j = y.(ae_time) !! j → x = y.

  Definition DBM_lsec_strongly_complete (j : nat) (s : gset apply_event) :=
    ∀ k, (1 ≤ k ∧ k <= length (elements (DBM_lsec j s))) ↔
         ∃ a, a ∈ (DBM_lsec j s) ∧ a.(ae_time) !! j = Some k.

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

  Lemma DBM_lsec_complete_DBM_lsec_times_j_NoDup j s :
    (∀ e, e ∈ s → length e.(ae_time) = length DB_addresses) →
    j < length DB_addresses →
    DBM_lsec_complete j s →
    ∃ l, map (λ e, e.(ae_time) !! j) (elements (DBM_lsec j s)) = map Some l ∧
         l ≡ₚ seq 1 (length l).
  Proof.
    intros Hl Hj Hcmp.
    exists (map (λ e : apply_event, default 0 (ae_time e !! j))
           (elements (DBM_lsec j s))).
    split.
    - apply list_eq; intros i.
      rewrite !list_lookup_fmap /=.
      destruct (elements (DBM_lsec j s) !! i) as [e|] eqn:Heq; simpl; last done.
      destruct (lookup_lt_is_Some_2 (ae_time e) j) as [x Hx];
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

  Lemma DBM_lsec_complete_DBM_lsec_ext j s :
    (∀ e, e ∈ s → length e.(ae_time) = length DB_addresses) →
    j < length DB_addresses →
    DBM_lsec_complete j s → DBM_lsec_ext j s.
  Proof.
    intros Htm Hj Hcmpl.
    destruct (DBM_lsec_complete_DBM_lsec_times_j_NoDup j s)
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

  Lemma DBM_LSV_ext {i j s} :
    (∀ e, e ∈ s → length e.(ae_time) = length DB_addresses) →
    j < length DB_addresses →
    DBM_lsec_valid i j s →
    DBM_lsec_ext j s.
  Proof.
    intros; apply DBM_lsec_complete_DBM_lsec_ext; eauto using DBM_LSV_comp.
  Qed.

  Lemma DBM_lsec_complete_DBM_lsec_strongly_complete j s :
    (∀ e, e ∈ s → length e.(ae_time) = length DB_addresses) →
    j < length DB_addresses →
    DBM_lsec_complete j s → DBM_lsec_strongly_complete j s.
  Proof.
    intros Htm Hj Hcmp.
    destruct (DBM_lsec_complete_DBM_lsec_times_j_NoDup j s)
      as (l & Hleq & Hlperm); [done|done|done|].
    intros k; split; first by apply Hcmp.
    intros (e & He1 & He2).
    rewrite -(map_length (λ e, ae_time e !! j)) Hleq map_length.
    assert (In k (seq 1 (length l))) as ?%in_seq; last lia.
    rewrite -Hlperm.
    apply elem_of_elements, elem_of_list_lookup_1 in He1 as [i He1].
    pose proof (f_equal (λ l, l !! i) Hleq) as Hleqi; simpl in *.
    rewrite !list_lookup_fmap He1 /= He2 in Hleqi.
    destruct (l !! i) eqn:Heq; last done; simplify_eq/=.
    apply elem_of_list_In, elem_of_list_lookup; eauto.
  Qed.

  Lemma DBM_LSV_strongly_complete {i j s} :
    (∀ e, e ∈ s → length e.(ae_time) = length DB_addresses) →
    j < length DB_addresses →
    DBM_lsec_valid i j s →
    DBM_lsec_strongly_complete j s.
  Proof.
    intros; apply DBM_lsec_complete_DBM_lsec_strongly_complete;
      eauto using DBM_LSV_comp.
  Qed.

  Lemma DBM_lsec_of_empty j : DBM_lsec j ∅ = ∅.
  Proof. by rewrite /DBM_lsec filter_empty_L. Qed.

  Lemma in_lsec_orig e s : e ∈ s → e ∈ DBM_lsec e.(ae_orig) s.
  Proof. by rewrite /DBM_lsec elem_of_filter. Qed.

  Lemma orig_in_lsec e j s : e ∈ DBM_lsec j s → ae_orig e = j.
  Proof. by rewrite /DBM_lsec elem_of_filter; intros [? ?]. Qed.

  Lemma in_lsec_in_lhst e j s : e ∈ DBM_lsec j s → e ∈ s.
  Proof. by rewrite /DBM_lsec elem_of_filter; intros [? ?]. Qed.

  Lemma DBM_lsec_latest_in_frame_empty j s x :
    DBM_lsec j s = ∅ → DBM_lsec_latest_in_frame j s x = 0.
  Proof.
    intros Hsec.
    symmetry; apply le_n_0_eq.
    rewrite /DBM_lsec_latest_in_frame.
    apply nat_sup_LUB.
    intros a.
    rewrite Hsec elements_empty filter_nil /=; inversion 1.
  Qed.

  Lemma sections_empty_valid i j :
    i < length DB_addresses →
    j < length DB_addresses →
    DBM_lsec_valid i j (DBM_lsec j ∅).
  Proof.
    split; [done|done| |done|done].
    intros ?.
    rewrite /DBM_lsec filter_empty_L elements_empty; simpl; lia.
  Qed.

  Lemma DBM_lsec_union j s s' :
    DBM_lsec j (s ∪ s') = DBM_lsec j s ∪ DBM_lsec j s'.
  Proof.
    apply set_eq; intros e.
    rewrite /DBM_lsec elem_of_union !elem_of_filter; set_solver.
  Qed.

  Lemma DBM_lsec_singleton_in j e :
    ae_orig e = j → DBM_lsec j {[e]} = {[e]}.
  Proof.
    intros ?; apply set_eq; intros e'.
    rewrite /DBM_lsec !elem_of_filter; set_solver.
  Qed.

  Lemma DBM_lsec_singleton_out j e :
    ae_orig e ≠ j → DBM_lsec j {[e]} = ∅.
  Proof.
    intros ?; apply set_eq; intros e'.
    rewrite /DBM_lsec !elem_of_filter; set_solver.
  Qed.

End Local_history_section_valid.
