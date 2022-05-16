From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Import model_update_prelude model_lst
     model_gst model_update_lhst model_update_lst.

Section Gst_update.
  Context `{!anerisG Mdl Σ, !RCB_params}.

   (** Global and local state coherence *)

  Lemma RCBM_gs_hst_valid_update gs i s h:
    RCBM_Gst_valid gs →
    RCBM_lhst_valid i s →
    RCBM_gs_hst_valid
      {| Gst_ghst := h; Gst_hst := <[i:=s]> (Gst_hst gs) |}.
  Proof.
    intros Hgv Hsv j sj Hgs; simpl.
    destruct (decide (j = i)) as [-> | ].
    - rewrite list_lookup_insert in Hgs.
      + by simplify_eq.
      + pose proof (RCBM_GV_hst_size Hgv).
        epose proof RCBM_LHV_bound_at.
        erewrite (RCBM_GV_hst_size Hgv); eauto.
    - rewrite list_lookup_insert_ne in Hgs; last done.
      eapply RCBM_GV_hst_lst_valid; eauto.
  Qed.

  Lemma RCBM_gs_hst_size_update gs i s h:
    RCBM_Gst_valid gs →
    RCBM_gs_hst_size
      {| Gst_ghst := h; Gst_hst := <[i:=s]> (Gst_hst gs) |}.
  Proof.
    intros Hgv. rewrite /RCBM_gs_hst_size //=.
    rewrite insert_length.
    by eapply RCBM_GV_hst_size.
  Qed.

  Lemma RCBM_system_write_update_gst (v : val) (i : nat) (gs : Gst) (ls : Lst) :
    RCBM_Lst_valid i ls →
    RCBM_Gst_valid gs →
    gs.(Gst_hst) !! i = Some ls.(Lst_hst) →
    let t := incr_time ls.(Lst_time) i  in
    let e := LocalEvent v t i (S (size ls.(Lst_hst))) in
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    let h := {[ erase e ]} ∪ gs.(Gst_ghst) in
    let Ss := <[i := s]> gs.(Gst_hst) in
    RCBM_Gst_valid (GST h Ss).
   Proof.
    intros Hvl Hvg Hgs t e s Ss.
    pose proof (RCBM_LSTV_at Hvl) as Hi.
    pose proof RCBM_LSTV_hst_valid Hvl as Hvlh.
    assert (update_condition i e (Lst_time ls)) as Hcond.
    eapply update_condition_write; eauto.
    pose proof Hcond as
            (Hi' & Htlen & Hetlen & Heorig & Het & Het' & Het'').
    split.
    - eapply RCBM_gs_hst_size_update; eauto.
    - eapply RCBM_gs_hst_valid_update; eauto.
      rewrite /RCBM_lst_hst_valid in Hvlh.
      eapply RCBM_lhst_update.
      + eauto.
      + eauto.
      + eauto.
      + eauto using RCBM_Lst_valid_time_le; eauto.
      + rewrite (RCBM_LSTV_time Hvl (le_orig e) Heorig).
        symmetry.
        pose proof (lsec_lsup_length (le_orig e)); eauto.
      + intros ? j0 Hj0.
        rewrite (RCBM_LSTV_time Hvl j0 Hj0).
        symmetry.
        pose proof (lsec_lsup_length (le_orig e)); eauto.
      + intros j0 Hj0.
        rewrite (RCBM_LSTV_time Hvl j0 Hj0).
        pose proof (lsec_lsup_length
                      i j0 (Lst_hst ls) Hvlh Hj0)
          as Hll. rewrite Hll.
        eauto with lia.
    - intros s1 Hs1 e1 He1. simpl in Hs1.
      subst Ss. apply elem_of_list_lookup in Hs1 as (j & Hs1).
      simpl.
      destruct (decide (i = j)) as [<-|Hneqij].
      + rewrite list_lookup_insert in Hs1. inversion Hs1. subst s1.
        clear Hs1. apply elem_of_union in He1 as [He1|?%elem_of_singleton_1].
        pose proof (λ H, RCBM_GV_hst_in_ghst Hvg (Lst_hst ls) H e1) as Hin.
        * apply elem_of_union; right.
          apply Hin; [eapply elem_of_list_lookup_2 |]; by eauto.
        * set_solver.
        * rewrite (RCBM_GV_hst_size Hvg) //.
      + rewrite list_lookup_insert_ne in Hs1; [ | done].
        pose proof (λ H, RCBM_GV_hst_in_ghst Hvg s1 H e1) as Hin.
        apply elem_of_union; right.
        apply Hin; [by eapply elem_of_list_lookup_2 | done].
    - intros a Hah.
      subst Ss s. simpl.
      apply elem_of_union in Hah as[ Ha1%elem_of_singleton_1 | Hrest].
      + assert (i = ge_orig a) as ->.
        { by rewrite Ha1 erase_orig. }
        rewrite list_lookup_insert.
        * eexists (Lst_hst ls ∪ {[e]}), _, e.
          repeat split; eauto.
          apply elem_of_filter; auto with set_solver.
        * assert (length (Gst_hst gs) = length RCB_addresses) as ->.
          { by apply RCBM_GV_hst_size. }
          done.
      + destruct (RCBM_GV_ghst_in_hst Hvg a Hrest) as (s1 & s2 & e' & Hs1 & Hlsec & Hin & ?).
        destruct (decide (i = ge_orig a)) as [->|Hneq].
        * rewrite list_lookup_insert; last first.
          {  assert (length (Gst_hst gs) = length RCB_addresses) as ->.
             { by apply RCBM_GV_hst_size. }
             done. }
          eexists _, _, _; repeat split; eauto.
          rewrite elem_of_filter; subst; split.
          { by rewrite erase_orig. }
          apply elem_of_union; left.
          apply elem_of_filter in Hin as [? ?].
          assert (Some s1 = Some (Lst_hst ls)) as Hsome.
          {  rewrite <- Hgs. rewrite <- Hs1. reflexivity. }
          inversion Hsome as [Heq]. by rewrite <- Heq.
        * rewrite list_lookup_insert_ne; [| done].
          eexists _, _, _; eauto.
    - simpl.
      intros a Hain.
      subst Ss.
      apply elem_of_union in Hain.
      destruct Hain as [Her%elem_of_singleton | Hings].
      + subst.
        subst e; subst t; simpl.
        rewrite incr_time_length.
        eapply RCBM_LSTV_time_length; eauto.
      + eapply RCBM_GstValid_time_length; eauto.
   Qed.

   Lemma RCBM_system_apply_update_gst
        (i : nat) (gs : Gst) (ls : Lst) (a : global_event) :
    RCBM_Gst_valid gs →
    RCBM_Lst_valid i ls →
    gs.(Gst_hst) !! i = Some ls.(Lst_hst) →
    a ∈ gs.(Gst_ghst) →
    a.(ge_orig) ≠ i →
    let e := LocalEvent (ge_payload a) (ge_time a) (ge_orig a)
                        (S (size ls.(Lst_hst))) in
    let s := ls.(Lst_hst) ∪ {[ e ]} in
    let Ss := (<[i := s]> gs.(Gst_hst)) in
    update_condition i e ls.(Lst_time) →
    RCBM_Gst_valid (GST gs.(Gst_ghst) Ss).
   Proof.
     intros Hvg Hvl Hgsi ??????.
     split.
     - eapply RCBM_gs_hst_size_update; eauto.
     - eapply RCBM_gs_hst_valid_update; eauto.
       remember (incr_time ls.(Lst_time) a.(ge_orig)) as t.
       assert (RCBM_Lst_valid i {| Lst_time := t; Lst_hst := s|})
         as Hvlst.
       { subst.
         apply (RCBM_lst_update e i ls Hvl); eauto. }
       eapply (RCBM_LSTV_hst_valid Hvlst).
     - intros s1 Hs1 e1 He1. simpl in Hs1.
       subst Ss. apply elem_of_list_lookup in Hs1 as (j & Hs1).
      destruct (decide (i = j)) as [<-|Hneqij].
      + rewrite list_lookup_insert in Hs1. inversion Hs1. subst s1.
        clear Hs1. apply elem_of_union in He1 as [He1|?%elem_of_singleton_1].
        * pose proof (λ H, RCBM_GV_hst_in_ghst Hvg (Lst_hst ls) H e1) as Himpl.
          apply Himpl; eauto using elem_of_list_lookup_2.
        * simpl. subst e1.
          assert (a = erase e) as <- by by destruct a.
          eauto.
        * rewrite (RCBM_GV_hst_size Hvg)  //.
          by eapply RCBM_LSTV_at.
      + rewrite list_lookup_insert_ne in Hs1; [| done].
        pose proof (λ H, RCBM_GV_hst_in_ghst Hvg s1 H e1) as Himpl.
        apply Himpl; eauto using elem_of_list_lookup_2.
     - intros a1 Ha1.
       destruct (decide (i = ge_orig a1)) as [Heq|Hneq].
       + assert
         (∃ (s0 si : gset local_event) (e0 : local_event),
             Gst_hst gs !! ge_orig a1 =
             Some s0 ∧ RCBM_lsec (ge_orig a1) s0 = si
             ∧ e0 ∈ si ∧ erase e0 = a1)
           as (s0 & si & e0 & Hs0 & Hs1 & Hs2 & Hs3)
             by by eapply RCBM_GV_ghst_in_hst.
         rewrite -!Heq. rewrite -!Heq in Hs0 Hs1.
         rewrite list_lookup_insert.
         * do 3 eexists. repeat split; eauto.
           rewrite /s. set_solver.
         * eapply lookup_lt_is_Some_1; eauto.
       + rewrite /Ss //=.
         rewrite list_lookup_insert_ne; eauto.
         eapply RCBM_GV_ghst_in_hst; eauto.
     - simpl.
      intros b Hbin.
      eapply RCBM_GstValid_time_length; eauto.
   Qed.

End Gst_update.
