(**  Mathematical model of the causal memory implementation
     from "Causal memory: definitions, implementation, and programming"
     (https://link.springer.com/article/10.1007/BF01784241).*)

From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Export model_lsec.

Section Local_history_valid.
  Context `{!anerisG Mdl Σ, !RCB_params}.

  Definition RCBM_lhst_ext (s : gset local_event) :=
    ∀ e e', e ∈ s → e' ∈ s → le_time e = le_time e' → e = e'.

  Definition RCBM_lhst_times (s : gset local_event) :=
    ∀ e, e ∈ s → length e.(le_time) = length RCB_addresses.

  Definition RCBM_lhst_origs (i : nat) (s : gset local_event) :=
    (∀ e, e ∈ s → e.(le_orig) < length RCB_addresses).

  Definition RCBM_lhst_lsec_valid (i : nat) (s : gset local_event) :=
    (∀ j, j < length RCB_addresses → RCBM_lsec_valid i j s).

  Definition RCBM_lhst_seqids (s : gset local_event) :=
    ∀ e, e ∈ s → e.(le_seqid) <= size s.

  Record RCBM_lhst_valid (i : nat) (s : gset local_event) : Prop := {
    RCBM_LHV_bound_at: i < length RCB_addresses;
    RCBM_LHV_times: RCBM_lhst_times s;
    RCBM_LHV_ext: RCBM_lhst_ext s;
    RCBM_LHV_origs: RCBM_lhst_origs i s;
    RCBM_LHV_secs_valid: RCBM_lhst_lsec_valid i s;
    RCBM_LHV_seqids: RCBM_lhst_seqids s;
  }.

  Global Arguments RCBM_LHV_bound_at {_ _} _.
  Global Arguments RCBM_LHV_times {_ _} _.
  Global Arguments RCBM_LHV_ext {_ _} _.
  Global Arguments RCBM_LHV_origs {_ _} _.
  Global Arguments RCBM_LHV_secs_valid {_ _} _.
  Global Arguments RCBM_LHV_seqids {_ _} _.

  Lemma in_lhs_time_component e k i s :
    RCBM_lhst_valid i s →
    k < length RCB_addresses →
    e ∈ s →
    is_Some (e.(le_time) !! k).
  Proof.
    intros ???; eapply lookup_lt_is_Some_2; erewrite RCBM_LHV_times; eauto.
  Qed.

  Lemma RCBM_lsec_empty i s:
    RCBM_lhst_valid i s →
    ∀ j', j' < length RCB_addresses →
          RCBM_lsec j' s = ∅ ↔ ∀ e, e ∈ s → e.(le_time) !! j' = Some 0.
  Proof.
    intros Hvli j' Hj'lt.
    split.
    - intros Hjs e Hes.
      pose proof (in_lsec_orig e s Hes) as Hesec.
      pose proof (RCBM_LHV_origs Hvli e Hes) as Heorig.
      destruct (lookup_lt_is_Some_2 (le_time e) j') as [k Hk].
      { rewrite (RCBM_LHV_times Hvli) //. }
      rewrite Hk.
      destruct (decide (j' = e.(le_orig))) as [->|].
      { by rewrite Hjs in Hesec. }
      pose proof (RCBM_LHV_secs_valid Hvli e.(le_orig) Heorig) as Hesecvl.
      destruct (decide (i = e.(le_orig))) as [->|].
      { pose proof (RCBM_LSV_caus_refl Hesecvl j' e Hj'lt) as Hvlrefl.
        rewrite Hk /= in Hvlrefl.
        rewrite RCBM_lsec_latest_in_frame_empty in Hvlrefl; last done.
        apply Hvlrefl; auto. }
      pose proof (RCBM_LSV_caus Hesecvl j' e Hj'lt) as Hvlirrefl.
      rewrite Hk /= in Hvlirrefl.
      rewrite RCBM_lsec_latest_in_frame_empty in Hvlirrefl; last done.
      f_equal; symmetry; apply le_n_0_eq.
      apply Hvlirrefl; auto.
    - destruct (decide (RCBM_lsec j' s = ∅)) as [|Hne]; first done.
      apply set_choose_L in Hne as [x Hx].
      pose proof (RCBM_LHV_secs_valid Hvli j' Hj'lt) as Hesecvl.
      intros He.
      pose proof (in_lsec_in_lhst _ _ _ Hx) as Hxs.
      apply He in Hxs.
      destruct (RCBM_LSV_strongly_complete (RCBM_LHV_times Hvli) Hj'lt Hesecvl 0)
        as [_ []]; eauto with lia.
  Qed.

  Definition lsec_sup (j : nat) (s: gset local_event) : nat :=
    nat_sup (omap (λ e, e.(le_time) !! j) (elements (RCBM_lsec j s))).

  Lemma lsec_sup_empty j : lsec_sup j ∅ = 0.
  Proof. by rewrite /lsec_sup RCBM_lsec_of_empty elements_empty /=. Qed.

  Lemma elem_of_lsec_lsec_sup_length e i j s :
    RCBM_lhst_valid i s →
    j < length RCB_addresses →
    e ∈ RCBM_lsec j s → length (elements (RCBM_lsec j s)) = lsec_sup j s.
  Proof.
    intros Hvl Hj He.
    assert (∃ e', e' ∈ RCBM_lsec j s ∧
                  (e'.(le_time) !! j = Some (lsec_sup j s))) as
        (e' & He'1 & He'2).
    { assert
        (lsec_sup j s ∈ (omap (λ e, e.(le_time) !! j)
                              (elements (RCBM_lsec j s)))) as Hsup.
      { edestruct (in_lhs_time_component e j) as [p Hp];
          eauto using in_lsec_in_lhst.
        eapply (nat_sup_elem_of p).
        apply elem_of_list_omap.
          by exists e; split; first apply elem_of_elements. }
      apply elem_of_list_omap in Hsup as (?&?%elem_of_elements&?); eauto. }
    apply Nat.le_antisymm.
    - edestruct le_lt_dec as [Hle|Hlt]; first exact Hle.
      destruct (RCBM_LSV_comp (RCBM_LHV_secs_valid Hvl j Hj) (S (lsec_sup j s))) as
          (e'' & He''1 & He''2); first lia.
      assert (S (lsec_sup j s) ≤ lsec_sup j s); last lia.
      apply nat_sup_UB.
      apply elem_of_list_omap.
        by eexists; split; first apply elem_of_elements.
    - apply (RCBM_LSV_strongly_complete
               (RCBM_LHV_times Hvl) Hj (RCBM_LHV_secs_valid Hvl j Hj)); eauto.
  Qed.

Lemma lsec_lsup_length i j s :
    RCBM_lhst_valid i s →
    j < length RCB_addresses →
    length (elements (RCBM_lsec j s)) = lsec_sup j s.
  Proof.
    intros Hvl Hj.
    destruct (decide (RCBM_lsec j s ≡ ∅)) as [Hempty| Hex].
    - rewrite /lsec_sup. simplify_eq. rewrite Hempty. set_solver.
    - apply set_choose in Hex as (e' & He').
      eapply (elem_of_lsec_lsec_sup_length e'); eauto.
  Qed.

  Lemma RCBM_lsec_causality_lemma i s e p q r :
    r < length RCB_addresses →
    RCBM_lhst_valid i s →
    e ∈ s →
    0 < p →
    p ≤ q →
    e.(le_time) !! r = Some q →
    ∃ e', e' ∈ RCBM_lsec r s ∧ e'.(le_time) !! r = Some p.
  Proof.
    intros Hr His He Hp Hpq Herq.
    destruct (decide (r = e.(le_orig))) as [Heq|Hreor].
    { apply (RCBM_LSV_comp (RCBM_LHV_secs_valid His r Hr)).
      split; first lia.
      apply (Nat.le_trans _ q); first done.
      apply (RCBM_LSV_strongly_complete
               (RCBM_LHV_times His) Hr (RCBM_LHV_secs_valid His r Hr)).
      exists e; split; last done.
        by rewrite Heq; apply in_lsec_orig. }
    assert (RCBM_lsec r s ≠ ∅) as Hrs.
    { rewrite (RCBM_lsec_empty i); auto.
      intros Hz.
      specialize (Hz e He); rewrite Herq in Hz; simplify_eq; lia. }
    assert (∃ e' p', e' ∈ RCBM_lsec r s ∧ e'.(le_time) !! r = Some p')
      as (e' & p' & He' & Hp').
    { apply set_choose_L in Hrs as (e' & He').
      edestruct (in_lhs_time_component e') as [p' Hp'];
        eauto using in_lsec_in_lhst. }
    assert (1 ≤ p').
    { eapply RCBM_LSV_strongly_complete; [|done| |by eauto].
      - by eapply RCBM_LHV_times; eauto.
      - by eapply RCBM_LHV_secs_valid; eauto. }
    assert (p' ≤ lsec_sup r s).
    { apply nat_sup_UB.
      apply elem_of_list_omap.
      exists e'; split; first apply elem_of_elements; eauto. }
    destruct (decide (p <= lsec_sup r s)).
    - assert (1 ≤ p ∧ p <= strings.length (elements (RCBM_lsec r s)))
        as Hpbounds.
      { split; first lia.
        erewrite elem_of_lsec_lsec_sup_length; eauto with lia. }
      apply (RCBM_LSV_comp (RCBM_LHV_secs_valid His r Hr)); eauto.
    - assert (lsec_sup r s < p) as HpSup by lia.
      assert (q <= lsec_sup r s); last lia.
      pose proof (RCBM_LHV_origs His e He) as Helsec.
      pose proof (RCBM_LSV_caus (RCBM_LHV_secs_valid His e.(le_orig) Helsec)
                               r e Hr Hreor) as Hq.
      rewrite Herq /= in Hq.
      etrans; first by apply Hq, in_lsec_orig.
      apply nat_sup_mono.
      intros a; rewrite !elem_of_list_omap;
        intros (?&[? ?]%elem_of_list_filter&?); eauto.
  Qed.

  Lemma empty_lhst_valid i :
    i < length RCB_addresses →
    RCBM_lhst_valid i ∅.
  Proof.
    split; [done|done|done|done| |done].
    intros ? ?; apply sections_empty_valid; done.
  Qed.

End Local_history_valid.
