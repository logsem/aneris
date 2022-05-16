From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import events model_update_prelude
     model_lst model_update_lsec model_update_lhst.

Section Lst_update.
  Context `{!anerisG Mdl Σ, !DB_params}.

  Lemma DBM_system_write_event_fresh_lhst e i d t s :
    (i < length t) →
    DBM_Lst_valid i {| Lst_mem := d; Lst_time := t; Lst_hst := s |} →
    e.(ae_time) = (incr_time t i) →
    e.(ae_orig) = i →
    e ∉ s.
  Proof.
    intros Hit Hvst Htime Horig Habs.
    apply (DBM_Lst_valid_time_le _ _ _ Hvst) in Habs.
    simpl in Habs; clear Hvst.
    apply incr_time_lt in Hit.
    apply vector_clock_le_eq_or_lt in Habs as [Habs | Habs].
    - assert (t = incr_time t i) as Htt by naive_solver.
      rewrite {1}Htt in Hit. by eapply vector_clock_lt_irreflexive.
    - rewrite Htime in Habs. eapply vector_clock_lt_exclusion; eauto.
  Qed.

  Lemma DBM_system_apply_event_fresh_lhst e i d t s :
    (i < length t) →
    e.(ae_orig) < length t →
    DBM_Lst_valid i {| Lst_mem := d; Lst_time := t; Lst_hst := s |} →
    e.(ae_time) !! e.(ae_orig) = Some (S (default 0 (t !! e.(ae_orig)))) →
    e.(ae_orig) ≠ i →
    e ∉ s.
  Proof.
    intros Hit Heot Hvst Htime Horig Habs.
    apply (DBM_Lst_valid_time_le _ _ _ Hvst) in Habs; simpl in *.
    eapply (Forall2_lookup_l _ _ _ _ _) in Habs; last done.
    destruct Habs as (?&->&Htt); simpl in *; lia.
  Qed.

  Lemma DBM_mem_dom_update {A: Type} k (v : A) (d: gmap Key A) :
    k ∈ DB_keys →
    dom d ⊆ DB_keys →
    dom (<[k:=v]> d) ⊆ DB_keys.
  Proof. by set_solver. Qed.

  Lemma DBM_lst_vals_some_update (ls : Lst) (i : nat) (e : apply_event) :
    DBM_Lst_valid i ls →
    e.(ae_seqid) = S (size ls.(Lst_hst)) →
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    let d := <[ e.(ae_key) := e.(ae_val) ]> ls.(Lst_mem) in
    update_condition i e ls.(Lst_time) →
    DBM_lst_vals_Some d s.
  Proof.
    intros Hvl Hid s d Hcnd.
    intros k1 v1 Hkv. subst s d.
    destruct (decide (e.(ae_key) = k1)) as [<-|Hneq]; last first.
    - rewrite restrict_key_union restrict_key_singleton_out;
          last eauto; rewrite union_empty_r_L.
        rewrite lookup_insert_ne in Hkv; last eauto.
          by eapply DBM_LSTV_vals_Some.
    - rewrite (Observe_lhst_max_seqid _ e); [| | |lia].
      + rewrite lookup_insert in Hkv; simplify_eq.
        split; first done.
        pose proof (update_condition_time _ _ _ Hcnd) as Ht.
        apply compute_maximals_correct.
        split.
        * rewrite restrict_key_union restrict_key_singleton_in; last done.
          set_solver.
        * intros e'.
          rewrite restrict_key_union restrict_key_singleton_in; last done.
          rewrite elem_of_union elem_of_singleton.
          intros [[? ?]%elem_of_filter| ->];
            last by apply vector_clock_lt_irreflexive.
          intros Hlt.
          apply Ht.
          eapply vector_clock_lt_le_trans; first apply Hlt.
          eapply DBM_Lst_valid_time_le; eauto.
      + intros e' He' He'e.
          rewrite Hid.
          eapply le_lt_trans;
            first apply (DBM_LHV_seqids (DBM_LSTV_hst_valid Hvl) e');
            last by simpl; lia.
          rewrite restrict_key_union restrict_key_singleton_in in He';
            set_solver.
      + rewrite restrict_key_union restrict_key_singleton_in; set_solver.
  Qed.

  Lemma DBM_lst_vals_none_update (ls : Lst) (i : nat) (e : apply_event) :
    DBM_Lst_valid i ls →
    let t := incr_time ls.(Lst_time) i in
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    let d := <[ e.(ae_key) := e.(ae_val) ]> ls.(Lst_mem) in
    update_condition i e ls.(Lst_time) →
    DBM_lst_vals_None d s.
   Proof.
     intros Hvl t s d Hcond k1 Hkv. subst t s d.
     destruct (decide (e.(ae_key) = k1)) as [<-|Hneq].
     - rewrite lookup_insert.
       rewrite restrict_key_union restrict_key_singleton_in; last eauto.
       set_solver.
     - rewrite lookup_insert_ne; last done.
       rewrite restrict_key_union restrict_key_singleton_out; last eauto.
       rewrite union_empty_r_L.
       eapply DBM_LSTV_vals_None; eauto.
   Qed.

  Lemma DBM_lst_time_update (i : nat) (ls : Lst) (e : apply_event) :
    DBM_Lst_valid i ls →
    e.(ae_seqid) = S (size ls.(Lst_hst)) →
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    update_condition i e ls.(Lst_time) →
    DBM_lst_time (incr_time ls.(Lst_time) e.(ae_orig)) s.
  Proof.
    simpl.
    intros Hvl Heseq Hcnd j Hj.
    destruct Hcnd as (Hi&Htlen&Hetlen&Hkey&Heorig&Het&Het'&Het'').
    destruct (decide (j = ae_orig e)) as [->|].
    - destruct (lookup_lt_is_Some_2 (Lst_time ls) (ae_orig e)) as [? Hte];
      first lia.
      rewrite Hte /= in Het.
      erewrite incr_time_proj; last done.
      f_equal.
      apply Nat.le_antisymm.
      + apply nat_sup_UB.
        rewrite elem_of_list_omap.
        setoid_rewrite elem_of_elements.
        setoid_rewrite DBM_lsec_union.
        setoid_rewrite DBM_lsec_singleton_in; last done.
        exists e; split; first set_solver; done.
      + apply nat_sup_LUB.
        intros n.
        rewrite elem_of_list_omap.
        setoid_rewrite elem_of_elements.
        setoid_rewrite DBM_lsec_union.
        setoid_rewrite elem_of_union.
        setoid_rewrite DBM_lsec_singleton_in; last done.
        setoid_rewrite elem_of_singleton.
        intros (e' & [He'1| ->] & He'2).
        * erewrite DBM_LSTV_time in Hte; eauto; simplify_eq.
          apply le_S.
          apply nat_sup_UB.
          rewrite elem_of_list_omap.
          setoid_rewrite elem_of_elements.
          eauto.
        * by rewrite Het in He'2; simplify_eq.
    - erewrite incr_time_proj_neq; last done.
      pose proof (DBM_LSTV_time Hvl j Hj) as ->.
      f_equal.
      apply nat_sup_equiv; intros m.
      rewrite !elem_of_list_omap.
      setoid_rewrite elem_of_elements.
      setoid_rewrite DBM_lsec_union.
      setoid_rewrite elem_of_union.
      setoid_rewrite DBM_lsec_singleton_out; last done.
      setoid_rewrite elem_of_empty.
      set_solver.
  Qed.

  Lemma DBM_lst_update (e : apply_event) (i : nat) (ls : Lst) :
    DBM_Lst_valid i ls →
    e.(ae_seqid) = S (size ls.(Lst_hst)) →
    let t := incr_time ls.(Lst_time) e.(ae_orig) in
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    let d := (<[ e.(ae_key) := e.(ae_val) ]> ls.(Lst_mem)) in
    update_condition i e ls.(Lst_time) →
    DBM_Lst_valid i (LST d t s).
  Proof.
    intros Hvl Hseq t s d Hcond.
    pose proof (DBM_LSTV_at Hvl).
    split; simpl.
    - done.
    - eapply DBM_mem_dom_update, DBM_LSTV_dom_keys.
        by destruct Hcond; by naive_solver; eauto. eauto.
    - eapply (DBM_lst_vals_some_update ls i e Hvl); eauto.
    - eapply (DBM_lst_vals_none_update ls i e Hvl); eauto.
    - eapply (DBM_lst_time_update i ls e Hvl Hseq Hcond); eauto.
    - subst t. rewrite /DBM_lst_time_length.
      erewrite incr_time_length. eapply DBM_LSTV_time_length; eauto.
    - pose proof Hcond as
            (Hi & Htlen & Hetlen & Hkey & Heorig & Het & Het' & Het'').
      eapply (DBM_lhst_update);
        [ eapply DBM_LSTV_hst_valid | done | done |  |  | | ];
        eauto using DBM_Lst_valid_time_le.
      + rewrite (DBM_LSTV_time Hvl (ae_orig e) Heorig).
        symmetry. f_equal.
        eapply (lsec_lsup_length i); eauto.
        eapply DBM_LSTV_hst_valid; eauto.
      + intros Heq j Hj.
        rewrite (DBM_LSTV_time Hvl j Hj).
        symmetry. f_equal.
        eapply (lsec_lsup_length i); eauto.
        eapply DBM_LSTV_hst_valid; eauto.
      +  intros j Hj.
         rewrite (DBM_LSTV_time Hvl j Hj).
         erewrite (lsec_lsup_length i); eauto.
         eapply DBM_LSTV_hst_valid; eauto.
  Qed.

  Lemma DBM_lst_update_write (e : apply_event) (i : nat) (ls : Lst) :
    DBM_Lst_valid i ls →
    e.(ae_key) ∈ DB_keys →
    e.(ae_seqid) = S (size ls.(Lst_hst)) →
    e.(ae_time) = incr_time ls.(Lst_time) i →
    e.(ae_orig) = i →
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    let d := <[ e.(ae_key) := e.(ae_val) ]> ls.(Lst_mem) in
    DBM_Lst_valid i (LST d e.(ae_time) s).
  Proof.
    intros Hvl Hek Heq Het Heo s d.
    pose proof (DBM_LSTV_at Hvl) as Hi.
    assert (update_condition i e (Lst_time ls)) as Hcond.
    eapply update_condition_write; eauto.
    pose proof (DBM_lst_update e i ls Hvl Heq Hcond).
    rewrite Het /d /s. by subst i.
  Qed.

  Lemma DBM_lst_update_apply (i : nat) (ls : Lst) (a : write_event) :
    a.(we_key) ∈ DB_keys →
    DBM_Lst_valid i ls →
    let t := incr_time ls.(Lst_time) a.(we_orig) in
    let e := ApplyEvent (we_key a) (we_val a) (we_time a) (we_orig a)
                        (S (size ls.(Lst_hst))) in
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    let d := (<[ a.(we_key) := a.(we_val) ]> ls.(Lst_mem)) in
    a.(we_orig) ≠ i →
    update_condition i e ls.(Lst_time) →
    DBM_Lst_valid i (LST d t s).
  Proof.
    intros Hk Hvl t e s d Horig Hcond.
    by eapply (DBM_lst_update e i ls Hvl).
  Qed.

End Lst_update.
