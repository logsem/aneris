From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import model_lst model_gst
     model_update_lhst model_update_lst model_update_gst.

Section System_update.
  Context `{!anerisG Mdl Σ, !DB_params}.

  Lemma DBM_system_write_event_fresh_gmem (e : apply_event) k v i d t s M Ss h :
    (i < length t) →
    DBM_Lst_valid i {| Lst_mem := d; Lst_time := t; Lst_hst := s |} →
    DBM_GstValid {| Gst_mem := M; Gst_hst := Ss |} →
    M !! k = Some h →
    Ss !! i = Some s →
    e = ApplyEvent k v (incr_time t i) i (S (length (elements s))) →
    e ∉ s →
    erase e ∉ h.
  Proof.
    intros Hit Hvlst Hvgst Hmk Hsi He Hes Habs.
    pose proof (DBM_GV_mem_in_hst Hvgst (erase e) h)
      as (si & sii & e' & Ha & Hvs & Hesi & Hers); try naive_solver.
    assert (si = s) as -> by naive_solver.
    assert (e' ∈ s).
    { eapply (in_lsec_in_lhst). by erewrite Hvs. }
    assert (we_time (erase e') = we_time (erase e) ∧ ae_orig e' = ae_orig e)
      as (Ht & Ho).
    { split; first by rewrite Hers.
      do 2 (rewrite -erase_orig). by rewrite Hers. }
    rewrite !erase_time in Ht.
    assert (e' ∉ s).
    { eapply (DBM_system_write_event_fresh_lhst e');  naive_solver. }
    done.
  Qed.


 Lemma DBM_system_write_event_maximum_lhst (e : apply_event) k v i d t s :
    (i < length t) →
    DBM_Lst_valid i {| Lst_mem := d; Lst_time := t; Lst_hst := s |} →
    e = ApplyEvent k v (incr_time t i) i (S (length (elements s))) →
    e ∉ s →
    (compute_maximum ae_time (s ∪ {[e]}) = Some e).
 Proof.
   intros ? Hvl Heeq ?.
   apply compute_maximum_correct.
   - eapply lhst_add_ext; first by eapply (DBM_LSTV_hst_valid Hvl); eauto.
     intros e' He' He'e.
     eapply (vector_clock_lt_irreflexive (ae_time e')).
     rewrite {2}He'e.
     rewrite Heeq /=.
     eapply vector_clock_le_lt_trans; last by apply incr_time_lt.
     eapply (DBM_Lst_valid_time_le _ {|Lst_time := t|}); done.
   - split.
     + apply elem_of_union; right; apply elem_of_singleton; done.
     + intros e' [?| ->%elem_of_singleton_1]%elem_of_union; last done.
       intros.
       eapply vector_clock_le_lt_trans;
         last by rewrite Heeq; apply incr_time_lt.
       eapply (DBM_Lst_valid_time_le _ {|Lst_time := t|}); done.
 Qed.

 Lemma DBM_system_write_event_maximals_gmem
       (e : apply_event) k v i d t s M Ss h :
    (i < length t) →
    DBM_Lst_valid i {| Lst_mem := d; Lst_time := t; Lst_hst := s |} →
    DBM_Gst_valid {| Gst_mem := M; Gst_hst := Ss |} →
    M !! k = Some h →
    Ss !! i = Some s →
    e = ApplyEvent k v (incr_time t i) i (S (length (elements s))) →
    e ∉ s →
    erase e ∉ h →
    erase e ∈ compute_maximals we_time (h ∪ {[erase e]}).
 Proof.
   intros Hit Hvlst Hvgst Hmk Hsi He Hes Heh.
   apply compute_maximals_correct; split; [ set_solver | ].
   intros a [ Ha | ?%elem_of_singleton_1]%elem_of_union Habs; last first.
   - by subst; eapply vector_clock_lt_irreflexive.
   - assert (∃ p,  0 < p ∧ a.(we_time) !! a.(we_orig) = Some p)
       as (aa & H_0_aa & H_aa) by by eapply we_in_valid_gs_time.
     assert (∃ k, t !! i = Some k) as (ti & H_ti)
         by by apply lookup_lt_is_Some_2.
     pose (ei := S ti).
     assert ((we_time (erase e)) !! i = Some ei) as H_ei.
     { rewrite erase_time; simplify_eq; by eapply incr_time_proj. }
     assert (∃ k, (we_time a) !! i = Some k ∧ ei <= k)
       as (ai & H_ai & H_ei_k).
     { apply vector_clock_lt_le in Habs.
         by eapply (Forall2_lookup_l _ _ (we_time a) i ei) in Habs. }
     assert (∃ (sa saa : gset apply_event) (e' : apply_event),
                Gst_hst {| Gst_mem := M; Gst_hst := Ss |}
                        !! we_orig a = Some sa
                ∧ DBM_lsec (we_orig a) sa = saa
                ∧ e' ∈ sa
                ∧ erase e' = a)
       as  (sa & saa & e' &  Hsa & Hsaa & He' & He'a).
     { epose proof (DBM_gs_mem_in_gs_hst_aux Hvgst a h k Hmk Ha) as
           (?&?&?&?&Hsec&?&?). destruct Hsec.
       do 3 eexists. repeat split; eauto using in_lsec_in_lhst. }
     destruct (decide (a.(we_orig) = i)) as [<- | Hneq].
     + subst ei a.
       assert (e' ∈ s) as He's by set_solver.
       assert (ae_time e' !! we_orig (erase e') = Some ai) as He'ai.
       { by rewrite -H_ai -erase_time. }
       assert (ai <= ti).
       { epose proof DBM_Lst_valid_time_le (we_orig (erase e'))
               _ e' Hvlst He's as Hlet.
         rewrite /vector_clock_le //= in Hlet.
         pose proof (Forall2_lookup_l le
                                       (ae_time e') t
                                       (we_orig (erase e'))
                                       ai Hlet He'ai)
           as
              (?&?&?).
         by simplify_eq. }
       lia.
     + assert (∃ e'', e'' ∈ DBM_lsec i sa ∧ (ae_time e'') !! i = Some ei)
         as (e'' & He'' & He''t).
       { eapply (DBM_lsec_causality_lemma _ _ e' ei ai);
           [by eapply DBM_LSTV_at|by eapply DBM_GV_hst_lst_valid|done| |done|];
           last first.
         { rewrite -erase_time He'a; done. }
         rewrite He /= in H_ei.
         erewrite incr_time_proj in H_ei; last done.
         simplify_eq; lia. }
       assert (∃ a'' h'', M !! e''.(ae_key) = Some h'' ∧
                          a'' ∈ h'' ∧ a''.(we_orig) = i ∧
                          a''.(we_time) !! i = Some ei ∧ a'' = erase e'')
         as (a'' & h'' & Hm'' & Ha'' & Ha''orig & Ha''time & Ha''e'').
       { destruct (λ H, DBM_GV_hst_in_mem Hvgst sa H e'')
           as (h' & Hh' & He''h'); simpl in *.
         { eapply elem_of_list_lookup_2; eauto. }
         { eapply in_lsec_in_lhst; eauto. }
         eexists (erase e''), _; split_and!; [done|done| | |done].
         - rewrite erase_orig; eapply orig_in_lsec; eauto.
         - rewrite erase_time; done. }
       assert (∃ ii, ii ∈ DBM_lsec i s ∧ (ae_time ii) !! i = Some ei) as
           (ii & Hii & Hiit).
       { destruct (DBM_GV_mem_in_hst Hvgst a'' h'')
           as (s0 & si & ei' & Ha''1 & Ha''2 & Ha''3 & Ha''4); [|done|].
         { by rewrite /= Ha''e'' erase_key. }
         rewrite Ha''orig /= Hsi in Ha''1; simplify_eq Ha''1; intros <-.
         rewrite -Ha''2 Ha''orig in Ha''3.
         exists ei'; split; first done.
         rewrite -erase_time Ha''4; done. }
       subst ei a.
       assert (ii ∈ s) as Hiis by set_solver.
       assert (S ti <= ti).
       { epose proof DBM_Lst_valid_time_le i _ ii Hvlst Hiis as Hlet.
         rewrite /vector_clock_le //= in Hlet.
         pose proof (Forall2_lookup_l le (ae_time ii) t i (S ti) Hlet Hiit)
           as (?&?&?).
           by simplify_eq. }
       lia.
 Qed.

End System_update.
