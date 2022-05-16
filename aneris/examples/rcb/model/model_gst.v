(**  Mathematical model of the causal memory implementation
     from "Causal memory: definitions, implementation, and programming"
     (https://link.springer.com/article/10.1007/BF01784241).*)

From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Export events model_spec model_lhst.

(** Global state validity implementation. *)
Section Global_state_valid.
  Context `{!anerisG Mdl Σ, !RCB_params}.

  (* The following two definitions capture the fact that the
       union of erasure of s_i (for i = 1 to n) is in M *)

  Definition RCBM_lhst_in_ghst (M : gset global_event)
             (s: gset local_event) :=
    ∀ e, e ∈ s → erase e ∈ M.

  Definition RCBM_gs_hst_in_gs_ghst (gs : Gst) : Prop :=
    ∀ s, s ∈ gs.(Gst_hst) → RCBM_lhst_in_ghst gs.(Gst_ghst) s.

  (* The following definition captures that the global events in the global
       history come from the sections s_ii (for i = 1 to n) *)
  Definition RCBM_gs_ghst_in_gs_hst (gs : Gst) :=
    ∀ a, a ∈ gs.(Gst_ghst) →
         ∃ s si e, gs.(Gst_hst) !! a.(ge_orig) = Some s ∧
                   RCBM_lsec a.(ge_orig) s = si ∧
                   e ∈ si ∧ erase e = a.

  Definition RCBM_gs_hst_valid (gs : Gst) :=
    ∀ i s, gs.(Gst_hst) !! i = Some s → RCBM_lhst_valid i s.

  Definition RCBM_gs_hst_size (gs : Gst) :=
    length gs.(Gst_hst) = length RCB_addresses.

  Definition RCBM_gs_vc_len (M : gset global_event) :=
    ∀ e, e ∈ M -> length e.(ge_time) = length RCB_addresses.

  (** Valid Global states *)
  Record RCBM_Gst_valid (gs: Gst) : Prop :=
    {
    RCBM_GV_hst_size : RCBM_gs_hst_size gs;
    RCBM_GV_hst_lst_valid : RCBM_gs_hst_valid gs ;
    RCBM_GV_hst_in_ghst : RCBM_gs_hst_in_gs_ghst gs;
    RCBM_GV_ghst_in_hst : RCBM_gs_ghst_in_gs_hst gs;
    RCBM_GV_vc_len :  RCBM_gs_vc_len gs.(Gst_ghst)
    }.

  Global Arguments RCBM_GV_hst_size {_} _.
  Global Arguments RCBM_GV_hst_lst_valid {_} _.
  Global Arguments RCBM_GV_hst_in_ghst {_} _.
  Global Arguments RCBM_GV_ghst_in_hst {_} _.
  Global Arguments RCBM_GV_vc_len {_} _.

  Lemma RCBM_gs_ghst_in_gs_hst_aux (gs : Gst) :
    RCBM_Gst_valid gs →
    ∀ a, a ∈ gs.(Gst_ghst) ->
         ∃ s si e, gs.(Gst_hst) !! a.(ge_orig) = Some s ∧
                   RCBM_lsec a.(ge_orig) s = si ∧
                   e ∈ si ∧ erase e = a .
  Proof.
    intros Hvg a Hah.
     by eapply RCBM_GV_ghst_in_hst.
  Qed.

  Global Arguments RCBM_gs_ghst_in_gs_hst_aux {_} _.

  Lemma RCBM_Gst_valid_hst_ith gs i s :
    RCBM_Gst_valid gs →
    gs.(Gst_hst) !! i = Some s →
    i < length RCB_addresses.
  Proof.
    intros Hvg His.
    apply lookup_lt_Some in His.
      by pose proof (RCBM_GV_hst_size Hvg) as <- .
  Qed.

  Lemma ge_in_valid_gs_orig gs a :
    RCBM_Gst_valid gs →
    a ∈ gs.(Gst_ghst) →
    a.(ge_orig) < length RCB_addresses.
  Proof.
    intros Hvg Ha.
    pose proof (RCBM_gs_ghst_in_gs_hst_aux Hvg a Ha)
      as (s & sr & e & Hs & <- & Her & Hea).
    pose proof (RCBM_GV_hst_lst_valid Hvg  (ge_orig a) s Hs).
      by eapply RCBM_LHV_bound_at.
  Qed.

  Lemma ge_in_valid_gs_vc_len gs a :
    RCBM_Gst_valid gs ->
    a ∈ gs.(Gst_ghst) ->
    length a.(ge_time) = length RCB_addresses.
  Proof.
    intros Hv Ha.
    eapply RCBM_GV_vc_len; eauto.
  Qed.

  Lemma ge_in_valid_gs_time gs a :
    RCBM_Gst_valid gs →
    a ∈ gs.(Gst_ghst) ->
    ∃ p, 0 < p ∧ a.(ge_time) !! a.(ge_orig) = Some p.
  Proof.
    intros Hvg Ha.
    pose proof (RCBM_gs_ghst_in_gs_hst_aux Hvg a Ha)
      as (s & sr & e & Hs & <- & Her & Hea); subst.
    pose proof (RCBM_GV_hst_lst_valid Hvg (ge_orig (erase e)) s Hs) as Hsv.
    assert ((erase e).(ge_orig) < length RCB_addresses) as Hao.
    { by eapply ge_in_valid_gs_orig. }
    pose proof (RCBM_LHV_secs_valid Hsv (ge_orig (erase e)) Hao) as Hsrv.
    assert (is_Some (le_time e !! (ge_orig (erase e)))) as [q Hq].
    eapply in_lhs_time_component;
      eauto using in_lsec_in_lhst.
    rewrite erase_time.
    exists q; split; try done.
    eapply RCBM_LSV_strongly_complete; [|done|by eauto|by eauto].
    eapply RCBM_LHV_times; eauto.
  Qed.

  Lemma RCBM_Gst_valid_empty : RCBM_Gst_valid empty_Gst.
  Proof.
    split; [| | | |];
      rewrite /empty_Gst /empty_ghst /empty_lhsts
              /RCBM_gs_hst_size /RCBM_gs_hst_valid
              /RCBM_gs_hst_in_gs_ghst /RCBM_gs_ghst_in_gs_hst
              //=.
    - by rewrite fmap_length.
    - intros ? ?; rewrite list_lookup_fmap.
      pose proof (lookup_lt_is_Some_1 RCB_addresses i).
      destruct (_ !! _); simpl; last done.
      intros ?; simplify_eq.
      apply empty_lhst_valid; eauto.
    - intros s.
      rewrite elem_of_list_fmap.
        by intros (?&->&?) ? ?.
  Qed.

  Lemma RCBM_Gst_valid_ghst_ext_internal (gs : Gst) (a a' : global_event) :
    RCBM_Gst_valid gs →
    a ∈ gs.(Gst_ghst) → a' ∈ gs.(Gst_ghst) →
    a.(ge_orig) = a'.(ge_orig) →
    a.(ge_time) !! a.(ge_orig) = a'.(ge_time) !! a.(ge_orig) →
    a = a'.
  Proof.
    intros Hvg Ha Ha' Horg Htime.
    pose proof (RCBM_gs_ghst_in_gs_hst_aux Hvg a Ha)
      as (s & sr & e & Hs & <- & Her & Hea); subst.
    pose proof (RCBM_gs_ghst_in_gs_hst_aux Hvg a' Ha')
      as (s' & sr' & e' & Hs' & <- & Her' & Hea'); subst.
    rewrite -Horg in Hs', Her'.
    assert (s' = s) as -> by naive_solver; clear Hs'.
    pose proof (RCBM_GV_hst_lst_valid Hvg  (ge_orig (erase e)) s Hs) as Hsv.
    assert ((erase e).(ge_orig) < length RCB_addresses) as Hao.
    { by eapply (ge_in_valid_gs_orig gs (erase e)). }
    pose proof (RCBM_LHV_secs_valid Hsv (ge_orig (erase e)) Hao) as Hsrv.
    pose proof (RCBM_LSV_ext (RCBM_LHV_times Hsv) Hao Hsrv) as Hext.
    f_equal.
      by apply Hext; auto; rewrite -!erase_time.
  Qed.

  Lemma RCBM_Gst_valid_ghst_ext (gs : Gst) (a1 a2 : global_event):
    RCBM_Gst_valid gs →
    a1 ∈ gs.(Gst_ghst) →
    a2 ∈ gs.(Gst_ghst) →
    (ge_time a1) = (ge_time a2) →
    a1 = a2.
  Proof.
    intros Hvg Hah Hah' Heq.
    destruct (decide (a1.(ge_orig) = a2.(ge_orig))) as [Horg | Horg ].
    - eapply (RCBM_Gst_valid_ghst_ext_internal gs); auto.
      rewrite Heq; done.
    - pose proof (RCBM_gs_ghst_in_gs_hst_aux Hvg a1 Hah)
        as (s & sr & e1 & Hs & <- & Her & Hea); subst.
      pose proof (RCBM_GV_hst_lst_valid Hvg _ _ Hs) as Hoe1s.
      pose proof (RCBM_gs_ghst_in_gs_hst_aux Hvg a2 Hah')
        as (s' & sr' & e2 & Hs' & <- & Her' & Hea'); subst.
      pose proof (RCBM_GV_hst_lst_valid Hvg _ _ Hs') as Hoe2s'.
      assert (ge_orig (erase e2) < length RCB_addresses) as He2dba
          by eauto using ge_in_valid_gs_orig.
      assert (∃ q, (erase e1).(ge_time) !! (ge_orig (erase e2)) = Some q)
        as [q Hq].
      { rewrite erase_time.
        destruct (in_lhs_time_component e1 (ge_orig (erase e2))
                                        (ge_orig (erase e1)) s);
          eauto using in_lsec_in_lhst, ge_in_valid_gs_orig. }
      destruct (RCBM_lsec_causality_lemma (ge_orig (erase e1)) s e1 q q
                                         (ge_orig (erase e2)))
        as (e12&He2s&He2tm); eauto using ge_in_valid_gs_orig, in_lsec_in_lhst.
      { eapply (RCBM_LSV_strongly_complete
                  (RCBM_LHV_times Hoe2s') He2dba
                  (RCBM_LHV_secs_valid Hoe2s' (ge_orig (erase e2)) He2dba)).
        eexists; split; eauto.
        rewrite -erase_time.
        rewrite -Heq; done. }
      { by rewrite -erase_time. }
      assert (e12 = e1) as He121.
      { eapply RCBM_LHV_ext; first apply Hoe1s; eauto using in_lsec_in_lhst.
        pose proof (RCBM_GV_hst_in_ghst Hvg) as Hgh.
        assert (s ∈ Gst_hst gs) as Hsgs by by apply elem_of_list_lookup; eauto.
        assert ( erase e12 ∈ Gst_ghst gs) as He12s. {
          apply (Hgh _ Hsgs e12).
          eauto using in_lsec_in_lhst. }
        rewrite -!erase_time.
        rewrite Heq.
        f_equal.
        symmetry.
        eapply (RCBM_Gst_valid_ghst_ext_internal _ _ _); eauto.
        - rewrite !erase_orig; erewrite !orig_in_lsec; eauto.
        - rewrite !erase_time He2tm.
          rewrite -erase_time.
          rewrite -Heq; done. }
      exfalso; apply Horg.
      rewrite -He121 erase_orig.
      erewrite orig_in_lsec; eauto.
  Qed.

  Lemma RCBM_Gst_valid_lhst_ext
        (gs : Gst) (i i' : nat) (s s' : gset local_event) (e e' : local_event):
    RCBM_Gst_valid gs →
    gs.(Gst_hst) !! i = Some s →  gs.(Gst_hst) !! i' = Some s' →
    e ∈ s → e' ∈ s' →
    le_time e = le_time e' →
    e.(le_payload) = e'.(le_payload) ∧
    e.(le_orig) = e'.(le_orig).
  Proof.
    intros Hgv ? ? He He' ?.
    rewrite -!erase_payload -!erase_orig.
    assert (erase e = erase e') as ->; last done.
    assert (s ∈ Gst_hst gs) as Hsin; [by eauto using elem_of_list_lookup_2 | ].
    pose proof (RCBM_GV_hst_in_ghst Hgv s Hsin) as Hlg.
    assert (s' ∈ Gst_hst gs) as Hsin'; [by eauto using elem_of_list_lookup_2 | ].
    pose proof (RCBM_GV_hst_in_ghst Hgv s' Hsin') as Hlg'.
    eapply (RCBM_Gst_valid_ghst_ext _ _ _); eauto.
    rewrite -> !erase_time; done.
  Qed.

  Lemma RCBM_Gst_valid_lhst_strong_ext
        (gs : Gst) (i : nat) (s : gset local_event) (e e' : local_event):
    RCBM_Gst_valid gs →
    gs.(Gst_hst) !! i = Some s →
    e ∈ s → e' ∈ s → le_time e = le_time e' → e = e'.
  Proof.
    intros Hgv ? He He' ?.
    eapply RCBM_LHV_ext; eauto.
    eapply RCBM_GV_hst_lst_valid; eauto.
  Qed.

  Lemma RCBM_Gst_valid_le_provenance (gs : Gst) (i : nat) (s : gset local_event)
        (e : local_event) :
    RCBM_Gst_valid gs → gs.(Gst_hst) !! i = Some s → e ∈ s →
    erase e ∈ gs.(Gst_ghst).
  Proof.
    intros; eapply RCBM_GV_hst_in_ghst; eauto using elem_of_list_lookup_2.
  Qed.

  Lemma RCBM_Gst_valid_ge_provenance (gs : Gst) (a : global_event) :
    RCBM_Gst_valid gs -> a ∈ gs.(Gst_ghst) ->
      ∃ s e, gs.(Gst_hst) !! a.(ge_orig) = Some s /\
             e ∈ s /\
             erase e = a.
  Proof.
    intros Hv Ha.
    pose proof (RCBM_GV_ghst_in_hst Hv a Ha) as [s [si [e (Hlook & Hsec & Hinsec & Herase)]]].
    assert (e ∈ RCBM_lsec (ge_orig a) s) as Hins; [set_solver|].
    apply in_lsec_in_lhst in Hins.
    eauto.
  Qed.

  Lemma RCBM_Gst_valid_causality
        (gs : Gst) (i : nat) (s : gset local_event)
        (e : local_event) (a : global_event) :
    RCBM_Gst_valid gs →
    gs.(Gst_hst) !! i = Some s →
    a ∈ gs.(Gst_ghst) → e ∈ s → vector_clock_lt (ge_time a) (le_time e) →
    ∃ e', e' ∈ s ∧ erase e' = a.
  Proof.
    intros Hvg His Hah Hes Hae.
    (* pose proof (RCBM_GV_ghst_elements_key Hvg k h a Hkh Hah) as ->. *)
    assert (∃ p,  0 < p ∧ a.(ge_time) !! a.(ge_orig) = Some p)
      as (p & H0p & Harp).
    { by eapply ge_in_valid_gs_time. }
    assert (∃ q, p <= q ∧ e.(le_time) !! a.(ge_orig) = Some q)
      as (q & Hpq & Herq).
    { pose proof (vector_clock_lt_le a.(ge_time) e.(le_time) Hae) as Hle.
      eapply Forall2_lookup_l in Hle as (q & Her & Hpq); eauto. }
    edestruct (RCBM_lsec_causality_lemma i s e p q) as (e' & He'rs & He'rp);
      eauto using ge_in_valid_gs_orig.
    { by eapply RCBM_GV_hst_lst_valid. }
    assert (le_orig e' = ge_orig a) as He'_orig.
    { by apply elem_of_filter in He'rs as (Horig&_). }
    assert (erase e' ∈ gs.(Gst_ghst)) as He'h'.
    { eapply RCBM_GV_hst_in_ghst; last eapply in_lsec_in_lhst; eauto.
      eapply elem_of_list_lookup_2; eauto. }
    assert (erase e' = a) as He'a.
    { eapply (RCBM_Gst_valid_ghst_ext_internal
                gs (erase e') a); try done.
      - rewrite -He'_orig. by apply erase_orig.
      - rewrite !erase_time !erase_orig.
          by rewrite !He'_orig Harp He'rp. }
    exists e'; split; last done.
    eauto using in_lsec_in_lhst.
  Qed.

  Global Instance db_states : RCB_global_state_valid :=
    {|
    RCBM_GstValid gs := RCBM_Gst_valid gs;
    RCBM_GstValid_empty := RCBM_Gst_valid_empty;
    RCBM_GstValid_lhst_size gs Hvg := Hvg.(RCBM_GV_hst_size);
    RCBM_GstValid_time_length := ge_in_valid_gs_vc_len;
    RCBM_GstValid_orig := ge_in_valid_gs_orig;
    RCBM_GstValid_ghst_ext := RCBM_Gst_valid_ghst_ext;
    RCBM_GstValid_lhst_ext := RCBM_Gst_valid_lhst_ext;
    RCBM_GstValid_lhst_strong_ext := RCBM_Gst_valid_lhst_strong_ext;
    RCBM_GstValid_le_provenance := RCBM_Gst_valid_le_provenance;
    RCBM_GstValid_ge_provenance := RCBM_Gst_valid_ge_provenance;
    RCBM_GstValid_causality := RCBM_Gst_valid_causality  |}.

End Global_state_valid.
