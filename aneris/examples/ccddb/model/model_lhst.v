(**  Mathematical model of the causal memory implementation
     from "Causal memory: definitions, implementation, and programming"
     (https://link.springer.com/article/10.1007/BF01784241).*)

From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Export model_lsec.

Section Local_history_valid.
  Context `{!anerisG Mdl Σ, !DB_params}.

  Definition DBM_lhst_ext (s : gset apply_event) :=
    ∀ e e', e ∈ s → e' ∈ s → ae_time e = ae_time e' → e = e'.

  Definition DBM_lhst_times (s : gset apply_event) :=
    ∀ e, e ∈ s → length e.(ae_time) = length DB_addresses.

  Definition DBM_lhst_origs (i : nat) (s : gset apply_event) :=
    (∀ e, e ∈ s → e.(ae_orig) < length DB_addresses).

  Definition DBM_lhst_lsec_valid (i : nat) (s : gset apply_event) :=
    (∀ j, j < length DB_addresses → DBM_lsec_valid i j s).

  Definition DBM_lhst_seqids (s : gset apply_event) :=
    ∀ e, e ∈ s → e.(ae_seqid) <= size s.

  Definition DBM_lhst_keys (s : gset apply_event) :=
    ∀ e, e ∈ s → e.(ae_key) ∈ DB_keys.

  Record DBM_lhst_valid (i : nat) (s : gset apply_event) : Prop := {
    DBM_LHV_bound_at: i < length DB_addresses;
    DBM_LHV_times: DBM_lhst_times s;
    DBM_LHV_ext: DBM_lhst_ext s;
    DBM_LHV_origs: DBM_lhst_origs i s;
    DBM_LHV_keys: DBM_lhst_keys s;
    DBM_LHV_secs_valid: DBM_lhst_lsec_valid i s;
    DBM_LHV_seqids: DBM_lhst_seqids s;
}.

  Global Arguments DBM_LHV_bound_at {_ _} _.
  Global Arguments DBM_LHV_times {_ _} _.
  Global Arguments DBM_LHV_ext {_ _} _.
  Global Arguments DBM_LHV_origs {_ _} _.
  Global Arguments DBM_LHV_secs_valid {_ _} _.
  Global Arguments DBM_LHV_seqids {_ _} _.
  Global Arguments DBM_LHV_keys {_ _} _.

  Lemma in_lhs_time_component e k i s :
    DBM_lhst_valid i s →
    k < length DB_addresses →
    e ∈ s →
    is_Some (e.(ae_time) !! k).
  Proof.
    intros ???; eapply lookup_lt_is_Some_2; erewrite DBM_LHV_times; eauto.
  Qed.

  Lemma DBM_lsec_empty i s:
    DBM_lhst_valid i s →
    ∀ j', j' < length DB_addresses →
          DBM_lsec j' s = ∅ ↔ ∀ e, e ∈ s → e.(ae_time) !! j' = Some 0.
  Proof.
    intros Hvli j' Hj'lt.
    split.
    - intros Hjs e Hes.
      pose proof (in_lsec_orig e s Hes) as Hesec.
      pose proof (DBM_LHV_origs Hvli e Hes) as Heorig.
      destruct (lookup_lt_is_Some_2 (ae_time e) j') as [k Hk].
      { rewrite (DBM_LHV_times Hvli) //. }
      rewrite Hk.
      destruct (decide (j' = e.(ae_orig))) as [->|].
      { by rewrite Hjs in Hesec. }
      pose proof (DBM_LHV_secs_valid Hvli e.(ae_orig) Heorig) as Hesecvl.
      destruct (decide (i = e.(ae_orig))) as [->|].
      { pose proof (DBM_LSV_caus_refl Hesecvl j' e Hj'lt) as Hvlrefl.
        rewrite Hk /= in Hvlrefl.
        rewrite DBM_lsec_latest_in_frame_empty in Hvlrefl; last done.
        apply Hvlrefl; auto. }
      pose proof (DBM_LSV_caus Hesecvl j' e Hj'lt) as Hvlirrefl.
      rewrite Hk /= in Hvlirrefl.
      rewrite DBM_lsec_latest_in_frame_empty in Hvlirrefl; last done.
      f_equal; apply Nat.le_0_r.
      apply Hvlirrefl; auto.
    - destruct (decide (DBM_lsec j' s = ∅)) as [|Hne]; first done.
      apply set_choose_L in Hne as [x Hx].
      pose proof (DBM_LHV_secs_valid Hvli j' Hj'lt) as Hesecvl.
      intros He.
      pose proof (in_lsec_in_lhst _ _ _ Hx) as Hxs.
      apply He in Hxs.
      destruct (DBM_LSV_strongly_complete (DBM_LHV_times Hvli) Hj'lt Hesecvl 0)
        as [_ []]; eauto with lia.
  Qed.

  Definition lsec_sup (j : nat) (s: gset apply_event) : nat :=
    nat_sup (omap (λ e, e.(ae_time) !! j) (elements (DBM_lsec j s))).

  Lemma lsec_sup_empty j : lsec_sup j ∅ = 0.
  Proof. by rewrite /lsec_sup DBM_lsec_of_empty elements_empty /=. Qed.

  Lemma elem_of_lsec_lsec_sup_length e i j s :
    DBM_lhst_valid i s →
    j < length DB_addresses →
    e ∈ DBM_lsec j s → length (elements (DBM_lsec j s)) = lsec_sup j s.
  Proof.
    intros Hvl Hj He.
    assert (∃ e', e' ∈ DBM_lsec j s ∧
                  (e'.(ae_time) !! j = Some (lsec_sup j s))) as
        (e' & He'1 & He'2).
    { assert
        (lsec_sup j s ∈ (omap (λ e, e.(ae_time) !! j)
                              (elements (DBM_lsec j s)))) as Hsup.
      { edestruct (in_lhs_time_component e j) as [p Hp];
          eauto using in_lsec_in_lhst.
        eapply (nat_sup_elem_of p).
        apply elem_of_list_omap.
          by exists e; split; first apply elem_of_elements. }
      apply elem_of_list_omap in Hsup as (?&?%elem_of_elements&?); eauto. }
    apply Nat.le_antisymm.
    - edestruct le_lt_dec as [Hle|Hlt]; first exact Hle.
      destruct (DBM_LSV_comp (DBM_LHV_secs_valid Hvl j Hj) (S (lsec_sup j s))) as
          (e'' & He''1 & He''2); first lia.
      assert (S (lsec_sup j s) ≤ lsec_sup j s); last lia.
      apply nat_sup_UB.
      apply elem_of_list_omap.
        by eexists; split; first apply elem_of_elements.
    - apply (DBM_LSV_strongly_complete
               (DBM_LHV_times Hvl) Hj (DBM_LHV_secs_valid Hvl j Hj)); eauto.
  Qed.

Lemma lsec_lsup_length i j s :
    DBM_lhst_valid i s →
    j < length DB_addresses →
    length (elements (DBM_lsec j s)) = lsec_sup j s.
  Proof.
    intros Hvl Hj.
    destruct (decide (DBM_lsec j s ≡ ∅)) as [Hempty| Hex].
    - rewrite /lsec_sup. simplify_eq. rewrite Hempty. set_solver.
    - apply set_choose in Hex as (e' & He').
      eapply (elem_of_lsec_lsec_sup_length e'); eauto.
  Qed.

  Lemma DBM_lsec_causality_lemma i s e p q r :
    r < length DB_addresses →
    DBM_lhst_valid i s →
    e ∈ s →
    0 < p →
    p ≤ q →
    e.(ae_time) !! r = Some q →
    ∃ e', e' ∈ DBM_lsec r s ∧ e'.(ae_time) !! r = Some p.
  Proof.
    intros Hr His He Hp Hpq Herq.
    destruct (decide (r = e.(ae_orig))) as [Heq|Hreor].
    { apply (DBM_LSV_comp (DBM_LHV_secs_valid His r Hr)).
      split; first lia.
      apply (Nat.le_trans _ q); first done.
      apply (DBM_LSV_strongly_complete
               (DBM_LHV_times His) Hr (DBM_LHV_secs_valid His r Hr)).
      exists e; split; last done.
        by rewrite Heq; apply in_lsec_orig. }
    assert (DBM_lsec r s ≠ ∅) as Hrs.
    { rewrite (DBM_lsec_empty i); auto.
      intros Hz.
      specialize (Hz e He); rewrite Herq in Hz; simplify_eq; lia. }
    assert (∃ e' p', e' ∈ DBM_lsec r s ∧ e'.(ae_time) !! r = Some p')
      as (e' & p' & He' & Hp').
    { apply set_choose_L in Hrs as (e' & He').
      edestruct (in_lhs_time_component e') as [p' Hp'];
        eauto using in_lsec_in_lhst. }
    assert (1 ≤ p').
    { eapply DBM_LSV_strongly_complete; [|done| |by eauto].
      - by eapply DBM_LHV_times; eauto.
      - by eapply DBM_LHV_secs_valid; eauto. }
    assert (p' ≤ lsec_sup r s).
    { apply nat_sup_UB.
      apply elem_of_list_omap.
      exists e'; split; first apply elem_of_elements; eauto. }
    destruct (decide (p <= lsec_sup r s)).
    - assert (1 ≤ p ∧ p <= strings.length (elements (DBM_lsec r s)))
        as Hpbounds.
      { split; first lia.
        erewrite elem_of_lsec_lsec_sup_length; eauto with lia. }
      apply (DBM_LSV_comp (DBM_LHV_secs_valid His r Hr)); eauto.
    - assert (lsec_sup r s < p) as HpSup by lia.
      assert (q <= lsec_sup r s); last lia.
      pose proof (DBM_LHV_origs His e He) as Helsec.
      pose proof (DBM_LSV_caus (DBM_LHV_secs_valid His e.(ae_orig) Helsec)
                               r e Hr Hreor) as Hq.
      rewrite Herq /= in Hq.
      etrans; first by apply Hq, in_lsec_orig.
      apply nat_sup_mono.
      intros a; rewrite !elem_of_list_omap;
        intros (?&[? ?]%elem_of_list_filter&?); eauto.
  Qed.

  Lemma empty_lhst_valid i :
    i < length DB_addresses →
    DBM_lhst_valid i ∅.
  Proof.
    split; [done|done|done|done|done| |done].
    intros ? ?; apply sections_empty_valid; done.
  Qed.

  Definition Observe_lhst (s : gset apply_event) : apply_event :=
    sup ae_seqid lt (ApplyEvent "" #() inhabitant 0 0) (elements s).

  Lemma Observe_lhst_max_seqid s e :
    (∀ e', e' ∈ s → e' ≠ e → e'.(ae_seqid) < e.(ae_seqid)) →
    e ∈ s →
    e.(ae_seqid) > 0 →
    Observe_lhst s = e.
  Proof.
    intros Hs Hes Heseq.
    assert (e.(ae_seqid) ≤ (Observe_lhst s).(ae_seqid)) as Hseqids.
    { apply (sup_UB ae_seqid lt le); last set_solver; eauto with lia. }
    assert (Observe_lhst s = (ApplyEvent "" #() inhabitant 0 0) ∨
            Observe_lhst s ∈ s) as Hobs.
    { rewrite -elem_of_elements.
      apply find_one_maximal_eq_or_elem_of. }
    destruct Hobs as [Hobs| Hobs].
    - rewrite Hobs in Hseqids; simpl in *; lia.
    - destruct (decide (Observe_lhst s = e)) as [|Hneq]; first done.
      specialize (Hs _ Hobs Hneq); lia.
  Qed.

  Lemma valid_lhst_restrict_key_out i s k :
    DBM_lhst_valid i s → k ∉ DB_keys → restrict_key k s = ∅.
  Proof.
    intros Hvl Hk.
    apply set_eq; intros a; split; last done.
    apply elem_of_subseteq; intros x.
    rewrite elem_of_filter.
    intros [<- Hx%(DBM_LHV_keys Hvl)]; done.
  Qed.

End Local_history_valid.
