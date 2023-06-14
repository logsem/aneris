From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import events model_lst
     model_update_prelude.

Section Lsec_udpate.
  Context `{!anerisG Mdl Σ, !DB_params}.

  Lemma update_condition_lsec_not_in e i t (s : gset apply_event) j :
    (i < length t) →
    (∀ e, e ∈ s → vector_clock_le e.(ae_time) t) →
    update_condition i e t →
    e ∉ DBM_lsec j s.
  Proof.
    intros Hjt Hst Hcnd Habs.
    apply (update_condition_time _ _ _ Hcnd).
    apply in_lsec_in_lhst in Habs.
      by pose proof  update_condition_lhst_not_in e i t s Hjt Hst Hcnd.
  Qed.

  (* NB: The assumption
    "t !! (ae_orig e) = Some (length (elements (DBM_lsec (ae_orig e) s))) →"
    is important and can be derived either from
    Local state validity or from dynamic check)
 *)
  Lemma DBM_lsec_complete_update e i j t s :
    DBM_lhst_valid i s →
    (∀ e, e ∈ s → vector_clock_le e.(ae_time) t) →
    ae_seqid e = S (size s) →
    update_condition i e t →
    j < length DB_addresses →
    t !! (ae_orig e) = Some (length (elements (DBM_lsec (ae_orig e) s))) →
    DBM_lsec_complete j (s ∪ {[e]}).
  Proof.
    intros His Hs Hseq Hcnd Hj Hte.
    destruct (decide (j = e.(ae_orig))) as [ Heq | Hneq ]; last first.
    - intros k.
      rewrite !DBM_lsec_union !DBM_lsec_singleton_out; last lia.
      rewrite right_id_L.
      intros; eapply DBM_LSV_comp; first apply DBM_LHV_secs_valid; eauto.
    - intro k.
      rewrite !DBM_lsec_union !DBM_lsec_singleton_in; last done.
      pose proof Hcnd as
          (Hi & Htlen & Hetlen & Hkey & Heorig & Het & Het' & Het'').
      destruct (lookup_lt_is_Some_2 (ae_time e) i) as [ti Hti];
        eauto with lia.
      rewrite (comm_L _ _ {[_]}) elements_union_singleton /=; last first.
      { eapply update_condition_lsec_not_in; eauto; lia. }
      pose proof (DBM_LHV_secs_valid His j Hj) as Hij.
      destruct (decide (k ≤ (length (elements (DBM_lsec j s))))).
      + intros [? ?].
        destruct (DBM_LSV_comp Hij k) as [x [Hx1 Hx2]]; first eauto with lia.
        set_solver.
      + intros [Hk1 Hk2].
         assert (k = S (length (elements (DBM_lsec j s))))
           as -> by by simpl in *; lia.
         exists e. split; first set_solver.
          subst j. by rewrite Het Hte.
  Qed.

  Lemma DBM_lsec_locally_causal_refl_update e i t s :
    DBM_lhst_valid i s →
    (∀ e, e ∈ s → vector_clock_le e.(ae_time) t) →
    ae_seqid e = S (size s) →
    update_condition i e t →
    (ae_orig e = i →
     ∀ j, j < length DB_addresses →
          t !! j = Some (length (elements (DBM_lsec j s)))) →
    DBM_lsec_locally_causal_refl i (s ∪ {[e]}).
  Proof.
    intros His Hs Hseq Hcnd Htj.
    intros j' ei Hj' Hij'
           [He'1 [He'2| ->%elem_of_singleton]%elem_of_union]%elem_of_filter.
    pose proof DBM_LHV_bound_at His as Hb.
    pose proof DBM_LHV_secs_valid His i Hb as Hsv.
    - (* i ≠ ae_orig e *)
      assert (ae_time ei !! j' = Some (DBM_lsec_latest_in_frame j' s ei)) as ->.
      { apply (DBM_LSV_caus_refl Hsv j' ei); eauto with lia.
        rewrite -He'1. by apply in_lsec_orig.  }
      rewrite /DBM_lsec_latest_in_frame. f_equal.
      apply nat_sup_equiv. intros k.
      rewrite !elem_of_list_omap.
      setoid_rewrite elem_of_list_filter.
      setoid_rewrite elem_of_elements.
      assert ( ae_seqid ei < ae_seqid e) as Hseqi.
      { pose proof DBM_LHV_seqids His ei He'2. lia. }
      split.
      + intros (x&[Hx1 Hxin]&Hx2).
        exists x; split_and!; [done| set_solver | done].
      + intros (x&[Hx1 Hxin]&Hx2).
            exists x; split_and!; [done|  | done].
            assert ( ae_seqid x < ae_seqid e) by lia.
            rewrite (DBM_lsec_union j' s {[e]})in Hxin.
            apply elem_of_union in Hxin as [Hx | Hx]; first done.
            rewrite /DBM_lsec in Hx.
            apply elem_of_filter in Hx as [? <-%elem_of_singleton].
            eauto with lia.
    - (* i = ae_orig e *)
      pose proof Hcnd as
          (Hi & Htlen & Hetlen & Hkey & Heorig & Het & Het' & Het'').
      specialize (Het'' He'1).
      specialize (Htj He'1).
      assert (ae_time e !! j' = t !! j') as Hetj'.
      { rewrite Het''. eapply incr_time_proj_neq; lia. }
      rewrite (Htj j' Hj') in Hetj'.
      rewrite Hetj'. f_equal.
      rewrite (lsec_lsup_length i); eauto.
      rewrite /DBM_lsec_latest_in_frame /lsec_sup.
       apply nat_sup_equiv.
      intros k.
      rewrite !elem_of_list_omap.
      setoid_rewrite elem_of_list_filter.
      setoid_rewrite elem_of_elements.
      split.
      + intros (x&Hxin&Hx2).
        exists x; split_and!; [| set_solver | done].
        eapply in_lsec_in_lhst in Hxin.
        pose proof DBM_LHV_seqids His x Hxin. lia.
      + intros (x&[Hx1 Hxin]&Hx2).
        exists x; split_and!; [  | done].
        assert ( ae_seqid x < ae_seqid e) by lia.
        rewrite (DBM_lsec_union j' s {[e]})in Hxin.
        apply elem_of_union in Hxin as [Hx | Hx]; first done.
        rewrite /DBM_lsec in Hx.
        apply elem_of_filter in Hx as [? <-%elem_of_singleton].
        eauto with lia.
  Qed.

  Lemma DBM_lsec_locally_causal_update e i j t s :
    DBM_lhst_valid i s →
    (∀ e, e ∈ s → vector_clock_le e.(ae_time) t) →
    ae_seqid e = S (size s) →
    update_condition i e t →
    j < length DB_addresses →
    (ae_orig e = i →
     ∀ j, j < length DB_addresses →
          t !! j = Some (length (elements (DBM_lsec j s)))) →
    (∀ j, j < length DB_addresses →
          default O (t !! j) <= (length (elements (DBM_lsec j s)))) →
    DBM_lsec_locally_causal j (s ∪ {[e]}).
  Proof.
    intros His Hs Hseq Hcnd Hj Htj Htj2.
     pose proof Hcnd as
        (Hi & Htlen & Hetlen & Hkey & Heorig & Het & Het' & Het'').
    destruct (decide (j = i)) as [->|].
    - assert (DBM_lsec_locally_causal_refl i (s ∪ {[e]})) as Hvlrefl.
      { eapply DBM_lsec_locally_causal_refl_update; eauto. }
      rewrite /DBM_lsec_locally_causal_refl in Hvlrefl.
      rewrite /DBM_lsec_locally_causal.
      intros j' x Hj' Hneq Hxin.
      destruct (lookup_lt_is_Some_2 (ae_time x) j') as [k Hk].
      {  rewrite DBM_lsec_union in Hxin.
         apply elem_of_union in Hxin as
             [[? Hx]%elem_of_filter |
              [? ->%elem_of_singleton ]%elem_of_filter].
         + pose proof DBM_LHV_times His x Hx. lia.
         + lia. }
      rewrite Hk.
      assert (ae_time x !! j' =
              Some (DBM_lsec_latest_in_frame j' (s ∪ {[e]}) x)) as Hx'.
        by eauto. rewrite -Hk Hx'. simpl. done.
    -  pose proof DBM_LHV_bound_at His as Hb.
       intros j' ei Hj' Hij'
              [He'1 [He'2| ->%elem_of_singleton]%elem_of_union]%elem_of_filter.
       + pose proof DBM_LHV_secs_valid His j Hj as Hvs.
         assert (from_option
                   (λ a : nat, a ≤ DBM_lsec_latest_in_frame j' s ei) False
                   (ae_time ei !! j')) as Hle.
         { apply (DBM_LSV_caus Hvs j' ei); eauto with lia.
           subst j. by apply in_lsec_orig. }
         destruct (lookup_lt_is_Some_2 (ae_time ei) j') as [k Hk].
          pose proof DBM_LHV_times His ei He'2. lia.
          rewrite Hk. rewrite Hk in Hle. simpl in *.
          trans (DBM_lsec_latest_in_frame j' s ei); first done.
          rewrite /DBM_lsec_latest_in_frame.
          apply nat_sup_mono.
         intros r Hr.
          rewrite !elem_of_list_omap.
          setoid_rewrite elem_of_list_filter.
          setoid_rewrite elem_of_elements.
          erewrite elem_of_list_omap in Hr.
          destruct Hr as (ej & Hej1 & Hej2).
          setoid_rewrite elem_of_list_filter in Hej1.
          destruct Hej1 as [? ?].
          exists ej. split_and!; [ |  | done]; eauto with lia.
          set_solver.
       +  assert (j' ≠ ae_orig e) as Hj'e by lia.
          specialize (Het' j' Hj' Hj'e).
          destruct (lookup_lt_is_Some_2 (ae_time e) j') as [k Hk];
            first eauto with lia.
          rewrite Hk in Het'. rewrite Hk. simpl in *.
          specialize (Htj2 j' Hj').
          trans (length (elements (DBM_lsec j' s))).
          * trans (default 0 (t !! j')); eauto with lia.
          *  erewrite (lsec_lsup_length i); eauto.
             rewrite /DBM_lsec_latest_in_frame /lsec_sup.
             apply nat_sup_mono.
             intros r Hr.
             rewrite !elem_of_list_omap.
             setoid_rewrite elem_of_list_filter.
             setoid_rewrite elem_of_elements.
             erewrite elem_of_list_omap in Hr.
             destruct Hr as (ej & Hej1 & Hej2).
             exists ej; split_and!; [| set_solver | done].
             rewrite /DBM_lsec in Hej1.
             erewrite elem_of_elements in Hej1.
             apply elem_of_filter in Hej1 as [? Hej1].
             pose proof DBM_LHV_seqids His ej Hej1.
             rewrite Hseq. by apply Nat.lt_succ_r.
  Qed.

  Lemma DBM_lhst_lsec_update e i t s :
    DBM_lhst_valid i s →
    (∀ e, e ∈ s → vector_clock_le e.(ae_time) t) →
    e.(ae_seqid) = (S (size s)) →
    update_condition i e t →
    t !! ae_orig e = Some (length (elements (DBM_lsec (ae_orig e) s))) →
    (ae_orig e = i
     → ∀ j, j < strings.length DB_addresses
            → t !! j = Some (length (elements (DBM_lsec j s)))) →
     (∀ j, j < length DB_addresses →
          default O (t !! j) <= (length (elements (DBM_lsec j s)))) →
    DBM_lhst_lsec_valid i (s ∪ {[ e ]}).
  Proof.
    intros.
    split.
    - eapply DBM_LHV_bound_at; eauto.
    - done.
    - eapply DBM_lsec_complete_update; eauto.
    - eapply DBM_lsec_locally_causal_refl_update; eauto.
    - eapply DBM_lsec_locally_causal_update; eauto.
  Qed.

End Lsec_udpate.
