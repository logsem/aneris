From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import model_update_prelude
     model_lhst model_update_lsec.

Section Lhst_udpate.
  Context `{!anerisG Mdl Σ, !DB_params}.

  Lemma lhst_add_ext i s e :
    DBM_lhst_valid i s →
    (∀ e', e' ∈ s → ae_time e' = ae_time e → False) →
    DBM_lhst_ext (s ∪ {[e]}).
  Proof.
    intros ? ? e1 e2
           [He1| ->%elem_of_singleton]%elem_of_union
           [He2| ->%elem_of_singleton]%elem_of_union;
      [by eapply DBM_LHV_ext| set_solver .. ].
  Qed.

  Lemma DBM_lhst_ext_update e i t s :
    DBM_lhst_valid i s →
    (∀ e, e ∈ s → vector_clock_le e.(ae_time) t) →
    update_condition i e t →
    DBM_lhst_ext (s ∪ {[e]}).
  Proof.
    intros His Ht Hcnd.
    eapply lhst_add_ext; first done.
    intros e1 He1 He1t.
    specialize (Ht e1 He1). rewrite He1t in Ht.
    assert (vector_clock_lt (ae_time e) t) as Hlt.
    { apply vector_clock_le_eq_or_lt in Ht as [ | ]; last done.
      subst. by eapply update_condition_absurd in Hcnd. }
    eapply update_condition_time; eauto.
  Qed.


  Lemma DBM_lhst_seqids_update e i t s :
    DBM_lhst_valid i s →
    e.(ae_seqid) = (S (size s)) →
    update_condition i e t →
    DBM_lhst_seqids (s ∪ {[e]}).
  Proof.
    intros Hvl Hseq Hcnd.
    pose proof Hcnd as
        (Hi & Htlen & Hetlen & Hkey & Heorig & Het & Het' & Het'').
    intros e' [ He' | ->%elem_of_singleton]%elem_of_union.
    + pose proof (DBM_LHV_seqids Hvl e' He').
      apply (Nat.le_trans _ (size s)); first done.
      by apply subseteq_size; set_solver.
    + rewrite size_union_alt.
      rewrite Hseq difference_disjoint_L;
          first by rewrite size_singleton; lia.
      apply elem_of_disjoint; intros ? ->%elem_of_singleton He.
        by pose proof (DBM_LHV_seqids Hvl e He); lia.
  Qed.

  Lemma DBM_lhst_origs_times_update e i t s :
    DBM_lhst_valid i s →
    update_condition i e t →
    let s' := (s ∪ {[e]}) in
    DBM_lhst_times s' ∧
    DBM_lhst_origs i s' ∧
    DBM_lhst_keys s'.
  Proof.
    simpl; intros Hvl Hcnd.
    destruct Hcnd as (Hi & Htlen & Hetlen & Hkey & Heorig & Het & Het' & Het'').
    repeat split; intros e' [ | ?%elem_of_singleton_1]%elem_of_union.
    - by eapply DBM_LHV_times.
    - set_solver.
    - by eapply DBM_LHV_origs.
    - set_solver.
    - by eapply DBM_LHV_keys.
    - set_solver.
  Qed.

  Lemma DBM_lhst_update e i t s :
    DBM_lhst_valid i s →
    update_condition i e t →
    e.(ae_seqid) = (S (size s)) →
    (∀ e : apply_event, e ∈ s → vector_clock_le (ae_time e) t) →
    t !! ae_orig e = Some (length (elements (DBM_lsec (ae_orig e) s))) →
    (ae_orig e = i
     → ∀ j, j < strings.length DB_addresses
            → t !! j = Some (length (elements (DBM_lsec j s)))) →
     (∀ j, j < length DB_addresses →
          default O (t !! j) <= (length (elements (DBM_lsec j s)))) →
     DBM_lhst_valid i (s ∪ {[ e ]}).
  Proof.
    intros Hvl Hcnd He Ht.
    pose proof Hcnd as (Hi & _).
    split; try eapply (DBM_lhst_origs_times_update e i t); eauto.
    - eapply DBM_lhst_ext_update; eauto.
    - eapply DBM_lhst_lsec_update; eauto.
    - eapply DBM_lhst_seqids_update; eauto.
  Qed.

End Lhst_udpate.
