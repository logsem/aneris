From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Import model_update_prelude
     model_lhst model_update_lsec.

Section Lhst_udpate.
  Context `{!anerisG Mdl Σ, !RCB_params}.

  Lemma lhst_add_ext i s e :
    RCBM_lhst_valid i s →
    (∀ e', e' ∈ s → le_time e' = le_time e → False) →
    RCBM_lhst_ext (s ∪ {[e]}).
  Proof.
    intros ? ? e1 e2
           [He1| ->%elem_of_singleton]%elem_of_union
           [He2| ->%elem_of_singleton]%elem_of_union;
      [by eapply RCBM_LHV_ext| set_solver .. ].
  Qed.

  Lemma RCBM_lhst_ext_update e i t s :
    RCBM_lhst_valid i s →
    (∀ e, e ∈ s → vector_clock_le e.(le_time) t) →
    update_condition i e t →
    RCBM_lhst_ext (s ∪ {[e]}).
  Proof.
    intros His Ht Hcnd.
    eapply lhst_add_ext; first done.
    intros e1 He1 He1t.
    specialize (Ht e1 He1). rewrite He1t in Ht.
    assert (vector_clock_lt (le_time e) t) as Hlt.
    { apply vector_clock_le_eq_or_lt in Ht as [ | ]; last done.
      subst. by eapply update_condition_absurd in Hcnd. }
    eapply update_condition_time; eauto.
  Qed.


  Lemma RCBM_lhst_seqids_update e i t s :
    RCBM_lhst_valid i s →
    e.(le_seqid) = (S (size s)) →
    update_condition i e t →
    RCBM_lhst_seqids (s ∪ {[e]}).
  Proof.
    intros Hvl Hseq Hcnd.
    pose proof Hcnd as
        (Hi & Htlen & Hetlen & Heorig & Het & Het' & Het'').
    intros e' [ He' | ->%elem_of_singleton]%elem_of_union.
    + pose proof (RCBM_LHV_seqids Hvl e' He').
      apply (Nat.le_trans _ (size s)); first done.
      by apply subseteq_size; set_solver.
    + rewrite size_union_alt.
      rewrite Hseq difference_disjoint_L;
          first by rewrite size_singleton; lia.
      apply elem_of_disjoint; intros ? ->%elem_of_singleton He.
        by pose proof (RCBM_LHV_seqids Hvl e He); lia.
  Qed.

  Lemma RCBM_lhst_origs_times_update e i t s :
    RCBM_lhst_valid i s →
    update_condition i e t →
    let s' := (s ∪ {[e]}) in
    RCBM_lhst_times s' ∧
    RCBM_lhst_origs i s'.
  Proof.
    simpl; intros Hvl Hcnd.
    destruct Hcnd as (Hi & Htlen & Hetlen & Heorig & Het & Het' & Het'').
    repeat split; intros e' [ | ?%elem_of_singleton_1]%elem_of_union.
    - by eapply RCBM_LHV_times.
    - set_solver.
    - by eapply RCBM_LHV_origs.
    - set_solver.
  Qed.

  Lemma RCBM_lhst_update e i t s :
    RCBM_lhst_valid i s →
    update_condition i e t →
    e.(le_seqid) = (S (size s)) →
    (∀ e : local_event, e ∈ s → vector_clock_le (le_time e) t) →
    t !! le_orig e = Some (length (elements (RCBM_lsec (le_orig e) s))) →
    (le_orig e = i
     → ∀ j, j < strings.length RCB_addresses
            → t !! j = Some (length (elements (RCBM_lsec j s)))) →
     (∀ j, j < length RCB_addresses →
          default O (t !! j) <= (length (elements (RCBM_lsec j s)))) →
     RCBM_lhst_valid i (s ∪ {[ e ]}).
  Proof.
    intros Hvl Hcnd He Ht.
    pose proof Hcnd as (Hi & _).
    split; try eapply (RCBM_lhst_origs_times_update e i t); eauto.
    - eapply RCBM_lhst_ext_update; eauto.
    - eapply RCBM_lhst_lsec_update; eauto.
    - eapply RCBM_lhst_seqids_update; eauto.
  Qed.

End Lhst_udpate.
