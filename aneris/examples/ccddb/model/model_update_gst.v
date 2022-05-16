From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import model_update_prelude model_lst
     model_gst model_update_lhst model_update_lst.

Section Gst_update.
  Context `{!anerisG Mdl Σ, !DB_params}.

   (** Global and local state coherence *)

  Lemma DBM_gs_ls_coh (i: nat) (gs : Gst) (ls : Lst) :
    i < length DB_addresses →
    DBM_Gst_valid gs →
    DBM_Lst_valid i ls →
    gs.(Gst_hst) !! i = Some ls.(Lst_hst) →
    dom ls.(Lst_mem) ⊆ dom gs.(Gst_mem) ∧
    ∀ k v, k ∈ DB_keys → ls.(Lst_mem) !! k = Some v →
           ∃ a h, gs.(Gst_mem) !! k = Some h ∧ a ∈ h ∧ a.(we_val) = v.
  Proof.
    intros.
    split.
    {  erewrite DBM_GstValid_dom; last done; by eapply DBM_LSTV_dom_keys. }
    intros k v Hk Hkv.
    eapply DBM_LSTV_vals_Some in Hkv as [Hv1 Hkv2]; eauto.
    set (Observe_lhst (restrict_key k (Lst_hst ls))) as e in *.
    apply compute_maximals_correct in Hkv2 as ([He Hem2]%elem_of_filter & Hem').
    eapply DBM_GV_hst_in_mem in Hem2 as (h & Hh & Heh);
      eauto using elem_of_list_lookup_2.
    simplify_eq/=.
    eexists (erase e), h; split_and!;
      [by rewrite -He|done|by rewrite -erase_val].
  Qed.

Lemma DBM_mem_dom_update {A: Type} k (v : A) (d: gmap Key A) :
    k ∈ DB_keys →
    dom d = DB_keys →
    dom (<[k:=v]> d) = DB_keys.
  Proof. by set_solver. Qed.

  Lemma DBM_gs_hst_valid_update gs i s m:
    DBM_Gst_valid gs →
    DBM_lhst_valid i s →
    DBM_gs_hst_valid
      {| Gst_mem := m; Gst_hst := <[i:=s]> (Gst_hst gs) |}.
  Proof.
    intros Hgv Hsv j sj Hgs; simpl.
    destruct (decide (j = i)) as [-> | ].
    - rewrite list_lookup_insert in Hgs.
      + by simplify_eq.
      + pose proof (DBM_GV_hst_size Hgv).
        epose proof DBM_LHV_bound_at.
        erewrite (DBM_GV_hst_size Hgv); eauto.
    - rewrite list_lookup_insert_ne in Hgs; last done.
      eapply DBM_GV_hst_lst_valid; eauto.
  Qed.

Lemma DBM_gs_hst_size_update gs i s m:
    DBM_Gst_valid gs →
    DBM_gs_hst_size
      {| Gst_mem := m; Gst_hst := <[i:=s]> (Gst_hst gs) |}.
  Proof.
    intros Hgv. rewrite /DBM_gs_hst_size //=.
    rewrite insert_length.
    by eapply DBM_GV_hst_size.
  Qed.

  Lemma DBM_system_write_update_gst
        (k : Key) (v : val) (i : nat) (gs : Gst) (ls : Lst) mk :
    k ∈ DB_keys →
    DBM_Lst_valid i ls →
    DBM_Gst_valid gs →
    gs.(Gst_hst) !! i = Some ls.(Lst_hst) →
    gs.(Gst_mem) !! k = Some mk →
    let t := incr_time ls.(Lst_time) i  in
    let e := ApplyEvent k v t i (S (size ls.(Lst_hst))) in
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    let m := (<[ k := mk ∪ {[erase e]} ]> gs.(Gst_mem)) in
    let Ss := <[i := s]> gs.(Gst_hst) in
    DBM_Gst_valid (GST m Ss).
   Proof.
    intros Hk Hvl Hvg Hgs Hgm t e s m Ss.
    pose proof (DBM_LSTV_at Hvl) as Hi.
    pose proof DBM_LSTV_hst_valid Hvl as Hvlh.
    assert (update_condition i e (Lst_time ls)) as Hcond.
    eapply update_condition_write; eauto.
    pose proof Hcond as
            (Hi' & Htlen & Hetlen & Hkey & Heorig & Het & Het' & Het'').
    split.
    - by eapply DBM_mem_dom_update; eauto; eapply DBM_GV_dom.
    - eapply DBM_gs_hst_size_update; eauto.
    - eapply DBM_gs_hst_valid_update; eauto.
      rewrite /DBM_lst_hst_valid in Hvlh.
      eapply DBM_lhst_update.
      + eauto.
      + eauto.
      + eauto.
      + eauto using DBM_Lst_valid_time_le; eauto.
      + rewrite (DBM_LSTV_time Hvl (ae_orig e) Heorig).
        symmetry.
        pose proof (lsec_lsup_length (ae_orig e)); eauto.
      + intros ? j0 Hj0.
        rewrite (DBM_LSTV_time Hvl j0 Hj0).
        symmetry.
        pose proof (lsec_lsup_length (ae_orig e)); eauto.
      + intros j0 Hj0.
        rewrite (DBM_LSTV_time Hvl j0 Hj0).
        pose proof (lsec_lsup_length
                      i j0 (Lst_hst ls) Hvlh Hj0)
          as Hll. rewrite Hll.
        eauto with lia.
    - intros s1 Hs1 e1 He1. simpl in Hs1.
      subst Ss. apply elem_of_list_lookup in Hs1 as (j & Hs1).
      destruct (decide (i = j)) as [<-|Hneqij].
      + rewrite list_lookup_insert in Hs1. inversion Hs1. subst s1.
        clear Hs1. apply elem_of_union in He1 as [He1|?%elem_of_singleton_1].
        * destruct (λ H, DBM_GV_hst_in_mem Hvg (Lst_hst ls) H e1)
            as (h' & Hh' & He''h'); eauto using elem_of_list_lookup_2.
          destruct (decide (k = ae_key e1)) as [->|Hneq].
          ** subst m; setoid_rewrite lookup_insert.
             exists (mk ∪ {[erase e]}); split; first done.
             rewrite Hgm // in Hh'. set_solver.
          ** subst m; setoid_rewrite lookup_insert_ne; last done.
             eexists; eauto.
        * simpl. subst e1 m.
          assert (k = ae_key e) as <- by eauto.
          setoid_rewrite lookup_insert.
          exists (mk ∪ {[erase e]}); split; first done.
          set_solver.
        * rewrite (DBM_GV_hst_size Hvg) //.
      + rewrite list_lookup_insert_ne in Hs1.
        destruct (λ H, DBM_GV_hst_in_mem Hvg s1 H e1)
          as (h' & Hh' & He''h'); eauto using elem_of_list_lookup_2.
        destruct (decide (k = ae_key e1)) as [->|Hneq]; simpl.
        * subst m.
          setoid_rewrite lookup_insert.
          rewrite Hh' in Hgm.
          eexists _. split_and!; eauto with set_solver.
        * exists h'; split_and!; eauto.
          by rewrite lookup_insert_ne; last done.
        * done.
    - intros a h Hm Hah.
      subst m Ss s. simpl in Hm. simpl.
      destruct (decide ((we_key a) = k)) as [ <- | Hneq0 ].
      + rewrite lookup_insert in Hm.
        simplify_eq.
        apply elem_of_union in Hah as[ Hamk| Ha1%elem_of_singleton_1].
        * destruct (DBM_GV_mem_in_hst Hvg a mk Hgm Hamk)
            as (sa & saa & ea & Hsa & Hsaa & Hea & Hear).
          destruct (decide (i = we_orig a)) as [Heq|Hneq].
          ** eexists (Lst_hst ls ∪ {[e]}), (saa ∪ {[e]}), ea.
             split_and!.
             *** subst; rewrite list_lookup_insert; first done.
                 rewrite (DBM_GV_hst_size Hvg) //.
             *** subst; rewrite //. set_solver.
             *** set_solver.
             *** done.
          ** eexists _, _, _.
             split_and!; eauto.
             by rewrite list_lookup_insert_ne.
        * eexists _, _, e.
          split_and!; eauto.
          ** rewrite Ha1. rewrite list_lookup_insert //=.
             rewrite (DBM_GV_hst_size Hvg) //.
          ** rewrite DBM_lsec_union DBM_lsec_singleton_in.
             *** set_solver.
             *** by rewrite Ha1.
      + rewrite lookup_insert_ne //= in Hm.
        destruct (decide (i = we_orig a)) as [Heq|Hneq].
       * assert
         (∃ (s0 si : gset apply_event) (e0 : apply_event),
             Gst_hst gs !! we_orig a =
             Some s0 ∧ DBM_lsec (we_orig a) s0 = si
             ∧ e0 ∈ si ∧ erase e0 = a)
           as (s0 & si & e0 & Hs0 & Hs1 & Hs2 & Hs3)
             by by eapply DBM_GV_mem_in_hst.
         rewrite -!Heq. rewrite -!Heq in Hs0 Hs1.
         rewrite list_lookup_insert.
         ** do 3 eexists. repeat split; eauto.
           rewrite /s0. set_solver.
         ** eapply lookup_lt_is_Some_1; eauto.
       * rewrite //=.
         simpl in Hm.
         rewrite list_lookup_insert_ne; eauto.
         eapply DBM_GV_mem_in_hst; eauto.
    - intros k1 h1 a1 Hh1 Ha1.
      rewrite /m //= in Hh1.
      destruct (decide (k1 = k)) as [-> | ].
      + rewrite lookup_insert //= in Hh1.
        simplify_eq.
        apply elem_of_union in Ha1 as [| ?%elem_of_singleton_1];
          [|set_solver].
        eapply DBM_GV_mem_elements_key; eauto.
      + rewrite lookup_insert_ne //= in Hh1.
        eapply DBM_GV_mem_elements_key; eauto.
   Qed.

   Lemma DBM_system_apply_update_gst
        (i : nat) (gs : Gst) (ls : Lst)
        (a : write_event) (h: gset write_event) :
    DBM_Gst_valid gs →
    DBM_Lst_valid i ls →
    gs.(Gst_hst) !! i = Some ls.(Lst_hst) →
    gs.(Gst_mem) !! a.(we_key) = Some h →
    a ∈ h →
    a.(we_orig) ≠ i →
    let t := incr_time ls.(Lst_time) a.(we_orig) in
    let e := ApplyEvent (we_key a) (we_val a) (we_time a) (we_orig a)
                        (S (size ls.(Lst_hst))) in
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    let d := (<[ a.(we_key) := a.(we_val) ]> ls.(Lst_mem)) in
    let Ss := (<[i := s]> gs.(Gst_hst)) in
    update_condition i e ls.(Lst_time) →
    DBM_Gst_valid (GST gs.(Gst_mem) Ss).
   Proof.
     intros Hvg Hvl Hgsi ?????????.
     split.
     - apply (DBM_GV_dom Hvg); eauto.
     - eapply DBM_gs_hst_size_update; eauto.
     - eapply DBM_gs_hst_valid_update; eauto.
       assert (DBM_Lst_valid i {|Lst_mem := d; Lst_time := t; Lst_hst := s|})
         as Hvlst.
       { apply (DBM_lst_update e i ls Hvl); eauto. }
       eapply (DBM_LSTV_hst_valid Hvlst).
     - intros s1 Hs1 e1 He1. simpl in Hs1.
       subst Ss. apply elem_of_list_lookup in Hs1 as (j & Hs1).
      destruct (decide (i = j)) as [<-|Hneqij].
      + rewrite list_lookup_insert in Hs1. inversion Hs1. subst s1.
        clear Hs1. apply elem_of_union in He1 as [He1|?%elem_of_singleton_1].
        * destruct (λ H, DBM_GV_hst_in_mem Hvg (Lst_hst ls) H e1)
            as (h' & Hh' & He''h'); eauto using elem_of_list_lookup_2.
        * simpl. subst e1.
          assert (a = erase e) as <- by by destruct a.
          eauto.
        * rewrite (DBM_GV_hst_size Hvg)  //.
          by eapply DBM_LSTV_at.
      + rewrite list_lookup_insert_ne in Hs1.
        destruct (λ H, DBM_GV_hst_in_mem Hvg s1 H e1)
          as (h' & Hh' & He''h'); eauto using elem_of_list_lookup_2.
        done.
     - intros a1 h1 Hm Ha1.
       destruct (decide (i = we_orig a1)) as [Heq|Hneq].
       + assert
         (∃ (s0 si : gset apply_event) (e0 : apply_event),
             Gst_hst gs !! we_orig a1 =
             Some s0 ∧ DBM_lsec (we_orig a1) s0 = si
             ∧ e0 ∈ si ∧ erase e0 = a1)
           as (s0 & si & e0 & Hs0 & Hs1 & Hs2 & Hs3)
             by by eapply DBM_GV_mem_in_hst.
         rewrite -!Heq. rewrite -!Heq in Hs0 Hs1.
         rewrite list_lookup_insert.
         * do 3 eexists. repeat split; eauto.
           rewrite /s. set_solver.
         * eapply lookup_lt_is_Some_1; eauto.
       + rewrite /Ss //=.
         simpl in Hm.
         rewrite list_lookup_insert_ne; eauto.
         eapply DBM_GV_mem_in_hst; eauto.
     - rewrite /DBM_gs_gmem_elements_key /=.
       eapply DBM_GV_mem_elements_key; eauto.
   Qed.

End Gst_update.
