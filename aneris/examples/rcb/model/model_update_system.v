From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Import model_lst model_gst
     model_update_lhst model_update_lst model_update_gst.

Section System_update.
  Context `{!anerisG Mdl Σ, !RCB_params}.


  Lemma RCBM_system_global_event_fresh_gmem (e : local_event) v i t s H' Ss :
    (i < length t) →
    RCBM_Lst_valid i {| Lst_time := t; Lst_hst := s |} →
    RCBM_GstValid {| Gst_ghst := H'; Gst_hst := Ss |} →
    Ss !! i = Some s →
    e = LocalEvent v (incr_time t i) i (S (length (elements s))) →
    e ∉ s →
    erase e ∉ H'.
  Proof.
    intros Hit Hvlst Hvgst Hsi He Hes Habs.
    pose proof (RCBM_GV_ghst_in_hst Hvgst (erase e) Habs)
      as (si & sii & e' & Ha & Hvs & Hesi & Hers); try naive_solver.
    assert (si = s) as -> by naive_solver.
    assert (e' ∈ s).
    { eapply (in_lsec_in_lhst). by erewrite Hvs. }
    assert (ge_time (erase e') = ge_time (erase e) ∧ le_orig e' = le_orig e)
      as (Ht & Ho).
    { split; first by rewrite Hers.
      do 2 (rewrite -erase_orig). by rewrite Hers. }
    rewrite !erase_time in Ht.
    assert (e' ∉ s).
    { eapply (RCBM_system_global_event_fresh_lhst e');  naive_solver. }
    done.
  Qed.


 Lemma RCBM_system_global_event_maximum_lhst (e : local_event) v i t s :
    (i < length t) →
    RCBM_Lst_valid i {| Lst_time := t; Lst_hst := s |} →
    e = LocalEvent v (incr_time t i) i (S (length (elements s))) →
    e ∉ s →
    (compute_maximum le_time (s ∪ {[e]}) = Some e).
 Proof.
   intros ? Hvl Heeq ?.
   apply compute_maximum_correct.
   - eapply lhst_add_ext; first by eapply (RCBM_LSTV_hst_valid Hvl); eauto.
     intros e' He' He'e.
     eapply (vector_clock_lt_irreflexive (le_time e')).
     rewrite {2}He'e.
     rewrite Heeq /=.
     eapply vector_clock_le_lt_trans; last by apply incr_time_lt.
     eapply (RCBM_Lst_valid_time_le _ {|Lst_time := t|}); done.
   - split.
     + apply elem_of_union; right; apply elem_of_singleton; done.
     + intros e' [?| ->%elem_of_singleton_1]%elem_of_union; last done.
       intros.
       eapply vector_clock_le_lt_trans;
         last by rewrite Heeq; apply incr_time_lt.
       eapply (RCBM_Lst_valid_time_le _ {|Lst_time := t|}); done.
 Qed.

 Lemma RCBM_system_global_event_maximals_gmem
       (e : local_event) v i t s H' Ss :
    (i < length t) →
    RCBM_Lst_valid i {| Lst_time := t; Lst_hst := s |} →
    RCBM_Gst_valid {| Gst_ghst := H'; Gst_hst := Ss |} →
    Ss !! i = Some s →
    e = LocalEvent v (incr_time t i) i (S (length (elements s))) →
    e ∉ s →
    erase e ∉ H' →
    erase e ∈ compute_maximals ge_time (H' ∪ {[erase e]}).
 Proof.
   intros Hit Hvlst Hvgst Hsi He Hes Heh.
   apply compute_maximals_correct; split; [ set_solver | ].
   intros a [ Ha | ?%elem_of_singleton_1]%elem_of_union Habs; last first.
   - by subst; eapply vector_clock_lt_irreflexive.
   - assert (∃ p,  0 < p ∧ a.(ge_time) !! a.(ge_orig) = Some p)
       as (aa & H_0_aa & H_aa) by by eapply ge_in_valid_gs_time.
     assert (∃ k, t !! i = Some k) as (ti & H_ti)
         by by apply lookup_lt_is_Some_2.
     pose (ei := S ti).
     assert ((ge_time (erase e)) !! i = Some ei) as H_ei.
     { rewrite erase_time; simplify_eq; by eapply incr_time_proj. }
     assert (∃ k, (ge_time a) !! i = Some k ∧ ei <= k)
       as (ai & H_ai & H_ei_k).
     { apply vector_clock_lt_le in Habs.
         by eapply (Forall2_lookup_l _ _ (ge_time a) i ei) in Habs. }
     assert (∃ (sa saa : gset local_event) (e' : local_event),
                Gst_hst {| Gst_ghst := H'; Gst_hst := Ss |}
                        !! ge_orig a = Some sa
                ∧ RCBM_lsec (ge_orig a) sa = saa
                ∧ e' ∈ sa
                ∧ erase e' = a)
       as  (sa & saa & e' &  Hsa & Hsaa & He' & He'a).
     { epose proof (RCBM_gs_ghst_in_gs_hst_aux Hvgst a Ha) as
           (?&?&?&?&Hsec&?&?). destruct Hsec.
       do 3 eexists. repeat split; eauto using in_lsec_in_lhst. }
     destruct (decide (a.(ge_orig) = i)) as [<- | Hneq].
     + subst ei a.
       assert (e' ∈ s) as He's by set_solver.
       assert (le_time e' !! ge_orig (erase e') = Some ai) as He'ai.
       { by rewrite -H_ai -erase_time. }
       assert (ai <= ti).
       { epose proof RCBM_Lst_valid_time_le (ge_orig (erase e'))
               _ e' Hvlst He's as Hlet.
         rewrite /vector_clock_le //= in Hlet.
         pose proof (Forall2_lookup_l le
                                       (le_time e') t
                                       (ge_orig (erase e'))
                                       ai Hlet He'ai)
           as
              (?&?&?).
         by simplify_eq. }
       lia.
     + assert (∃ e'', e'' ∈ RCBM_lsec i sa ∧ (le_time e'') !! i = Some ei)
         as (e'' & He'' & He''t).
       { eapply (RCBM_lsec_causality_lemma _ _ e' ei ai);
           [by eapply RCBM_LSTV_at|by eapply RCBM_GV_hst_lst_valid|done| |done|];
           last first.
         { rewrite -erase_time He'a; done. }
         rewrite He /= in H_ei.
         erewrite incr_time_proj in H_ei; last done.
         simplify_eq; lia. }
       assert (∃ a'', a'' ∈ H' ∧ a''.(ge_orig) = i ∧
                      a''.(ge_time) !! i = Some ei ∧ a'' = erase e'')
         as (a'' & Ha'' & Ha''orig & Ha''time & Ha''e'').
       { pose proof (λ H, RCBM_GV_hst_in_ghst Hvgst sa H e'') as Hin.
         simpl in *.
         assert (sa ∈ Ss) as HinSs.
         { eapply elem_of_list_lookup_2; eauto. }
         assert (e'' ∈ sa) as Hinsa.
         { eapply in_lsec_in_lhst; eauto. }
         pose proof (Hin HinSs Hinsa) as Hin'.
         eexists (erase e''). split_and!; [done| |  |done].
         - rewrite erase_orig; eapply orig_in_lsec; eauto.
         - rewrite erase_time; done. }
       assert (∃ ii, ii ∈ RCBM_lsec i s ∧ (le_time ii) !! i = Some ei) as
           (ii & Hii & Hiit).
       { destruct (RCBM_GV_ghst_in_hst Hvgst a'')
           as (s0 & si & ei' & Ha''1 & Ha''2 & Ha''3 & Ha''4); [done |].
         rewrite Ha''orig /= Hsi in Ha''1; simplify_eq Ha''1; intros <-.
         rewrite -Ha''2 Ha''orig in Ha''3.
         exists ei'; split; first done.
         rewrite -erase_time Ha''4; done. }
       subst ei a.
       assert (ii ∈ s) as Hiis by set_solver.
       assert (S ti <= ti).
       { epose proof RCBM_Lst_valid_time_le i _ ii Hvlst Hiis as Hlet.
         rewrite /vector_clock_le //= in Hlet.
         pose proof (Forall2_lookup_l le (le_time ii) t i (S ti) Hlet Hiit)
           as (?&?&?).
           by simplify_eq. }
       lia.
 Qed.

End System_update.
