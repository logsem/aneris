From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Import events model_update_prelude
     model_lst model_update_lsec model_update_lhst.

Section Lst_update.
  Context `{!anerisG Mdl Σ, !RCB_params}.

  Lemma RCBM_system_global_event_fresh_lhst e i t s :
    (i < length t) →
    RCBM_Lst_valid i {| Lst_time := t; Lst_hst := s |} →
    e.(le_time) = (incr_time t i) →
    e.(le_orig) = i →
    e ∉ s.
  Proof.
    intros Hit Hvst Htime Horig Habs.
    apply (RCBM_Lst_valid_time_le _ _ _ Hvst) in Habs.
    simpl in Habs; clear Hvst.
    apply incr_time_lt in Hit.
    apply vector_clock_le_eq_or_lt in Habs as [Habs | Habs].
    - assert (t = incr_time t i) as Htt by naive_solver.
      rewrite {1}Htt in Hit. by eapply vector_clock_lt_irreflexive.
    - rewrite Htime in Habs. eapply vector_clock_lt_exclusion; eauto.
  Qed.

  Lemma RCBM_system_local_event_fresh_lhst e i t s :
    (i < length t) →
    e.(le_orig) < length t →
    RCBM_Lst_valid i {| Lst_time := t; Lst_hst := s |} →
    e.(le_time) !! e.(le_orig) = Some (S (default 0 (t !! e.(le_orig)))) →
    e.(le_orig) ≠ i →
    e ∉ s.
  Proof.
    intros Hit Heot Hvst Htime Horig Habs.
    apply (RCBM_Lst_valid_time_le _ _ _ Hvst) in Habs; simpl in *.
    eapply (Forall2_lookup_l _ _ _ _ _) in Habs; last done.
    destruct Habs as (?&->&Htt); simpl in *; lia.
  Qed.

  Lemma RCBM_lst_time_update (i : nat) (ls : Lst) (e : local_event) :
    RCBM_Lst_valid i ls →
    e.(le_seqid) = S (size ls.(Lst_hst)) →
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    update_condition i e ls.(Lst_time) →
    RCBM_lst_time (incr_time ls.(Lst_time) e.(le_orig)) s.
  Proof.
    simpl.
    intros Hvl Heseq Hcnd j Hj.
    destruct Hcnd as (Hi&Htlen&Hetlen&Heorig&Het&Het'&Het'').
    destruct (decide (j = le_orig e)) as [->|].
    - destruct (lookup_lt_is_Some_2 (Lst_time ls) (le_orig e)) as [? Hte];
      first lia.
      rewrite Hte /= in Het.
      erewrite incr_time_proj; last done.
      f_equal.
      apply Nat.le_antisymm.
      + apply nat_sup_UB.
        rewrite elem_of_list_omap.
        setoid_rewrite elem_of_elements.
        setoid_rewrite RCBM_lsec_union.
        setoid_rewrite RCBM_lsec_singleton_in; last done.
        exists e; split; first set_solver; done.
      + apply nat_sup_LUB.
        intros n.
        rewrite elem_of_list_omap.
        setoid_rewrite elem_of_elements.
        setoid_rewrite RCBM_lsec_union.
        setoid_rewrite elem_of_union.
        setoid_rewrite RCBM_lsec_singleton_in; last done.
        setoid_rewrite elem_of_singleton.
        intros (e' & [He'1| ->] & He'2).
        * erewrite RCBM_LSTV_time in Hte; eauto; simplify_eq.
          apply le_S.
          apply nat_sup_UB.
          rewrite elem_of_list_omap.
          setoid_rewrite elem_of_elements.
          eauto.
        * by rewrite Het in He'2; simplify_eq.
    - erewrite incr_time_proj_neq; last done.
      pose proof (RCBM_LSTV_time Hvl j Hj) as ->.
      f_equal.
      apply nat_sup_equiv; intros m.
      rewrite !elem_of_list_omap.
      setoid_rewrite elem_of_elements.
      setoid_rewrite RCBM_lsec_union.
      setoid_rewrite elem_of_union.
      setoid_rewrite RCBM_lsec_singleton_out; last done.
      setoid_rewrite elem_of_empty.
      set_solver.
  Qed.

  Lemma RCBM_lst_update (e : local_event) (i : nat) (ls : Lst) :
    RCBM_Lst_valid i ls →
    e.(le_seqid) = S (size ls.(Lst_hst)) →
    let t := incr_time ls.(Lst_time) e.(le_orig) in
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    update_condition i e ls.(Lst_time) →
    RCBM_Lst_valid i (LST t s).
  Proof.
    intros Hvl Hseq t s Hcond.
    pose proof (RCBM_LSTV_at Hvl).
    split; simpl.
    - done.
    - eapply (RCBM_lst_time_update i ls e Hvl Hseq Hcond); eauto.
    - subst t. rewrite /RCBM_lst_time_length.
      erewrite incr_time_length. eapply RCBM_LSTV_time_length; eauto.
    - pose proof Hcond as
            (Hi & Htlen & Hetlen & Heorig & Het & Het' & Het'').
      eapply (RCBM_lhst_update);
        [ eapply RCBM_LSTV_hst_valid | done | done |  |  | | ];
        eauto using RCBM_Lst_valid_time_le.
      + rewrite (RCBM_LSTV_time Hvl (le_orig e) Heorig).
        symmetry. f_equal.
        eapply (lsec_lsup_length i); eauto.
        eapply RCBM_LSTV_hst_valid; eauto.
      + intros Heq j Hj.
        rewrite (RCBM_LSTV_time Hvl j Hj).
        symmetry. f_equal.
        eapply (lsec_lsup_length i); eauto.
        eapply RCBM_LSTV_hst_valid; eauto.
      +  intros j Hj.
         rewrite (RCBM_LSTV_time Hvl j Hj).
         erewrite (lsec_lsup_length i); eauto.
         eapply RCBM_LSTV_hst_valid; eauto.
  Qed.

  Lemma RCBM_lst_update_write (e : local_event) (i : nat) (ls : Lst) :
    RCBM_Lst_valid i ls →
    e.(le_seqid) = S (size ls.(Lst_hst)) →
    e.(le_time) = incr_time ls.(Lst_time) i →
    e.(le_orig) = i →
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    RCBM_Lst_valid i (LST e.(le_time) s).
  Proof.
    intros Hvl Heq Het Heo s.
    pose proof (RCBM_LSTV_at Hvl) as Hi.
    assert (update_condition i e (Lst_time ls)) as Hcond.
    eapply update_condition_write; eauto.
    pose proof (RCBM_lst_update e i ls Hvl Heq Hcond).
    rewrite Het /s. by subst i.
  Qed.

  Lemma RCBM_lst_update_apply (i : nat) (ls : Lst) (a : global_event) :
    RCBM_Lst_valid i ls →
    let t := incr_time ls.(Lst_time) a.(ge_orig) in
    let e := LocalEvent (ge_payload a) (ge_time a) (ge_orig a)
                        (S (size ls.(Lst_hst))) in
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    a.(ge_orig) ≠ i →
    update_condition i e ls.(Lst_time) →
    RCBM_Lst_valid i (LST t s).
  Proof.
    intros Hvl t e s Horig Hcond.
    by eapply (RCBM_lst_update e i ls Hvl).
  Qed.

End Lst_update.
