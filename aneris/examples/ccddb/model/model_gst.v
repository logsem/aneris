(**  Mathematical model of the causal memory implementation
     from "Causal memory: definitions, implementation, and programming"
     (https://link.springer.com/article/10.1007/BF01784241).*)

From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Export events model_spec model_lhst.

(** Global state validity implementation. *)
Section Global_state_valid.
  Context `{!anerisG Mdl Σ, !DB_params}.

  (* The following two definitions capture the fact that the
       union of erasure of s_i (for i = 1 to n) is in M *)

  Definition DBM_lhst_in_gmem (M : gmap Key (gset write_event))
             (s: gset apply_event) :=
    ∀ e, e ∈ s → ∃ h, M !! e.(ae_key) = Some h ∧ erase e ∈ h.

  Definition DBM_gs_hst_in_gs_mem (gs : Gst) : Prop :=
    ∀ s, s ∈ gs.(Gst_hst) → DBM_lhst_in_gmem gs.(Gst_mem) s.

  (* The following definition captures that the write events in the global
       memory come from the sections s_ii (for i = 1 to n) *)
  Definition DBM_gs_mem_in_gs_hst (gs : Gst) :=
    ∀ a h, gs.(Gst_mem) !! a.(we_key) = Some h → a ∈ h →
           ∃ s si e, gs.(Gst_hst) !! a.(we_orig) = Some s ∧
                     DBM_lsec a.(we_orig) s = si ∧
                     e ∈ si ∧ erase e = a.

  Definition DBM_gs_hst_valid (gs : Gst) :=
    ∀ i s, gs.(Gst_hst) !! i = Some s → DBM_lhst_valid i s.

  Definition DBM_dom (gs : Gst) :=
    dom gs.(Gst_mem) = DB_keys.

  Definition DBM_gs_hst_size (gs : Gst) :=
    length gs.(Gst_hst) = length DB_addresses.

  Definition DBM_gs_gmem_elements_key (gs : Gst) :=
    ∀ k h a, gs.(Gst_mem) !! k = Some h → a ∈ h → k = a.(we_key).

  (** Valid Global states *)
  Record DBM_Gst_valid (gs: Gst) : Prop :=
    {
    DBM_GV_dom : DBM_dom gs;
    DBM_GV_hst_size : DBM_gs_hst_size gs;
    DBM_GV_hst_lst_valid : DBM_gs_hst_valid gs ;
    DBM_GV_hst_in_mem : DBM_gs_hst_in_gs_mem gs;
    DBM_GV_mem_in_hst : DBM_gs_mem_in_gs_hst gs;
    DBM_GV_mem_elements_key : DBM_gs_gmem_elements_key gs;
    }.

  Global Arguments DBM_GV_dom {_} _.
  Global Arguments DBM_GV_hst_size {_} _.
  Global Arguments DBM_GV_hst_lst_valid {_} _.
  Global Arguments DBM_GV_hst_in_mem {_} _.
  Global Arguments DBM_GV_mem_in_hst {_} _.
  Global Arguments DBM_GV_mem_elements_key {_} _.

  Lemma DBM_gs_mem_in_gs_hst_aux (gs : Gst) :
    DBM_Gst_valid gs →
    ∀ a h k, gs.(Gst_mem) !! k = Some h → a ∈ h →
             ∃ s si e, gs.(Gst_hst) !! a.(we_orig) = Some s ∧
                       DBM_lsec a.(we_orig) s = si ∧
                       e ∈ si ∧ erase e = a .
  Proof.
    intros Hvg a h k Hkh Hah.
    pose proof (DBM_GV_mem_elements_key Hvg k h a Hkh Hah) as ->.
      by eapply DBM_GV_mem_in_hst.
  Qed.

  Global Arguments DBM_gs_mem_in_gs_hst_aux {_} _.

  Lemma DBM_Gst_valid_hst_ith gs i s :
    DBM_Gst_valid gs →
    gs.(Gst_hst) !! i = Some s →
    i < length DB_addresses.
  Proof.
    intros Hvg His.
    apply lookup_lt_Some in His.
      by pose proof (DBM_GV_hst_size Hvg) as <- .
  Qed.

  Lemma we_in_valid_gs_orig gs k a h :
    DBM_Gst_valid gs →
    gs.(Gst_mem) !! k = Some h → a ∈ h →
    a.(we_orig) < length DB_addresses.
  Proof.
    intros Hvg Hkh Hak.
    pose proof (DBM_gs_mem_in_gs_hst_aux Hvg a h k Hkh Hak)
      as (s & sr & e & Hs & <- & Her & Hea).
    pose proof (DBM_GV_hst_lst_valid Hvg  (we_orig a) s Hs).
      by eapply DBM_LHV_bound_at.
  Qed.

  Lemma we_in_valid_gs_time gs k a h :
    DBM_Gst_valid gs →
    gs.(Gst_mem) !! k = Some h → a ∈ h →
    ∃ p, 0 < p ∧ a.(we_time) !! a.(we_orig) = Some p.
  Proof.
    intros Hvg Hkh Hak.
    pose proof (DBM_gs_mem_in_gs_hst_aux Hvg a h k Hkh Hak)
      as (s & sr & e & Hs & <- & Her & Hea); subst.
    pose proof (DBM_GV_hst_lst_valid Hvg (we_orig (erase e)) s Hs) as Hsv.
    assert ((erase e).(we_orig) < length DB_addresses) as Hao.
    { by eapply we_in_valid_gs_orig. }
    pose proof (DBM_LHV_secs_valid Hsv (we_orig (erase e)) Hao) as Hsrv.
    assert (is_Some (ae_time e !! (we_orig (erase e)))) as [q Hq].
    eapply in_lhs_time_component;
      eauto using in_lsec_in_lhst.
    rewrite erase_time.
    exists q; split; try done.
    eapply DBM_LSV_strongly_complete; [|done|by eauto|by eauto].
    eapply DBM_LHV_times; eauto.
  Qed.

  Lemma DBM_Gst_valid_empty : DBM_Gst_valid empty_Gst.
  Proof.
    split; [| | | | |];
      rewrite /empty_Gst /empty_gmem /empty_lhsts
              /DBM_dom /DBM_gs_hst_size /DBM_gs_hst_valid
              /DBM_gs_hst_in_gs_mem /DBM_gs_mem_in_gs_hst
              / DBM_gs_gmem_elements_key //=.
    - eauto using dom_gset_to_gmap.
    - by rewrite fmap_length.
    - intros ? ?; rewrite list_lookup_fmap.
      pose proof (lookup_lt_is_Some_1 DB_addresses i).
      destruct (_ !! _); simpl; last done.
      intros ?; simplify_eq.
      apply empty_lhst_valid; eauto.
    - intros s.
      rewrite elem_of_list_fmap.
        by intros (?&->&?) ? ?.
    - intros a ?; rewrite lookup_gset_to_gmap.
      destruct (decide (we_key a ∈ DB_keys));
        last by rewrite option_guard_False.
        by rewrite option_guard_True //; intros ?; simplify_eq.
    - intros k ? ?; rewrite lookup_gset_to_gmap.
      destruct (decide (k ∈ DB_keys));
        last by rewrite option_guard_False.
        by rewrite option_guard_True //; intros ?; simplify_eq.
  Qed.

  Lemma DBM_Gst_valid_gmem_ext_internal
        (gs : Gst) (k k' : Key) (h h' : gset write_event) (a a' : write_event) :
    DBM_Gst_valid gs →
    gs.(Gst_mem) !! k = Some h → gs.(Gst_mem) !! k' = Some h' →
    a ∈ h → a' ∈ h' →
    a.(we_orig) = a'.(we_orig) →
    a.(we_time) !! a.(we_orig) = a'.(we_time) !! a.(we_orig) →
    a = a'.
  Proof.
    intros Hvg Hkh Hkh' Hak Hak' Horg Htime.
    pose proof (DBM_gs_mem_in_gs_hst_aux Hvg a h k Hkh Hak)
      as (s & sr & e & Hs & <- & Her & Hea); subst.
    pose proof (DBM_gs_mem_in_gs_hst_aux Hvg a' h' k' Hkh' Hak')
      as (s' & sr' & e' & Hs' & <- & Her' & Hea'); subst.
    rewrite -Horg in Hs', Her'.
    assert (s' = s) as -> by naive_solver; clear Hs'.
    pose proof (DBM_GV_hst_lst_valid Hvg  (we_orig (erase e)) s Hs) as Hsv.
    assert ((erase e).(we_orig) < length DB_addresses) as Hao.
    { by eapply (we_in_valid_gs_orig gs _ (erase e) h). }
    pose proof (DBM_LHV_secs_valid Hsv (we_orig (erase e)) Hao) as Hsrv.
    pose proof (DBM_LSV_ext (DBM_LHV_times Hsv) Hao Hsrv) as Hext.
    f_equal.
      by apply Hext; auto; rewrite -!erase_time.
  Qed.

  Lemma DBM_Gst_valid_gmem_ext_internal_2
        (gs : Gst) (k k' : Key) (h h' : gset write_event) (a1 a2 : write_event):
    DBM_Gst_valid gs →
    gs.(Gst_mem) !! k = Some h → gs.(Gst_mem) !! k' = Some h' →
    a1 ∈ h → a2 ∈ h' → (we_time a1) = (we_time a2) → a1 = a2.
  Proof.
    intros Hvg Hkh Hkh' Hah Hah' Heq.
    destruct (decide (a1.(we_orig) = a2.(we_orig))) as [Horg | Horg ].
    - eapply (DBM_Gst_valid_gmem_ext_internal gs k k' h h'); auto.
      rewrite Heq; done.
    - pose proof (DBM_gs_mem_in_gs_hst_aux Hvg a1 h k Hkh Hah)
        as (s & sr & e1 & Hs & <- & Her & Hea); subst.
      pose proof (DBM_GV_hst_lst_valid Hvg _ _ Hs) as Hoe1s.
      pose proof (DBM_gs_mem_in_gs_hst_aux Hvg a2 h' k' Hkh' Hah')
        as (s' & sr' & e2 & Hs' & <- & Her' & Hea'); subst.
      pose proof (DBM_GV_hst_lst_valid Hvg _ _ Hs') as Hoe2s'.
      assert (we_orig (erase e2) < length DB_addresses) as He2dba
          by eauto using we_in_valid_gs_orig.
      assert (∃ q, (erase e1).(we_time) !! (we_orig (erase e2)) = Some q)
        as [q Hq].
      { rewrite erase_time.
        destruct (in_lhs_time_component e1 (we_orig (erase e2))
                                        (we_orig (erase e1)) s);
          eauto using in_lsec_in_lhst, we_in_valid_gs_orig. }
      destruct (DBM_lsec_causality_lemma (we_orig (erase e1)) s e1 q q
                                         (we_orig (erase e2)))
        as (e12&He2s&He2tm); eauto using we_in_valid_gs_orig, in_lsec_in_lhst.
      { eapply (DBM_LSV_strongly_complete
                  (DBM_LHV_times Hoe2s') He2dba
                  (DBM_LHV_secs_valid Hoe2s' (we_orig (erase e2)) He2dba)).
        eexists; split; eauto.
        rewrite -erase_time.
        rewrite -Heq; done. }
      { by rewrite -erase_time. }
      assert (e12 = e1) as He121.
      { eapply DBM_LHV_ext; first apply Hoe1s; eauto using in_lsec_in_lhst.
        pose proof (DBM_GV_hst_in_mem Hvg) as Hgh.
        assert (s ∈ Gst_hst gs) as Hsgs by by apply elem_of_list_lookup; eauto.
        destruct (Hgh _ Hsgs e12) as (h'' & Hh''1 & He12);
          first by eauto using in_lsec_in_lhst.
        rewrite -!erase_time.
        rewrite Heq.
        f_equal.
        symmetry.
        eapply (DBM_Gst_valid_gmem_ext_internal _ _ _ h' h''); eauto.
        - rewrite !erase_orig; erewrite !orig_in_lsec; eauto.
        - rewrite !erase_time He2tm.
          rewrite -erase_time.
          rewrite -Heq; done. }
      exfalso; apply Horg.
      rewrite -He121 erase_orig.
      erewrite orig_in_lsec; eauto.
  Qed.

  Lemma DBM_Gst_valid_gmem_ext
        (gs : Gst) (k k' : Key) (h h' : gset write_event) (a a' : write_event):
    DBM_Gst_valid gs →
    gs.(Gst_mem) !! k = Some h → gs.(Gst_mem) !! k' = Some h' →
    a ∈ h → a' ∈ h' → we_time a = we_time a' → a = a'.
  Proof.
    intros Hvg Hkh Hkh' Hah Hah' Heq.
    apply (DBM_Gst_valid_gmem_ext_internal_2 gs k k' h h'); eauto.
  Qed.

  Lemma DBM_Gst_valid_lhst_ext
        (gs : Gst) (i i' : nat) (s s' : gset apply_event) (e e' : apply_event):
    DBM_Gst_valid gs →
    gs.(Gst_hst) !! i = Some s →  gs.(Gst_hst) !! i' = Some s' →
    e ∈ s → e' ∈ s' → ae_time e = ae_time e' →
    e.(ae_key) = e'.(ae_key) ∧ e.(ae_val) = e'.(ae_val).
  Proof.
    intros Hgv ? ? He He' ?.
    rewrite -!erase_key -!erase_val.
    assert (erase e = erase e') as ->; last done.
    edestruct (DBM_GV_hst_in_mem Hgv s) as (h & Hh & Hea);
      eauto using elem_of_list_lookup_2.
    edestruct (DBM_GV_hst_in_mem Hgv s') as (h' & Hh' & Hea');
      eauto using elem_of_list_lookup_2.
    eapply (DBM_Gst_valid_gmem_ext_internal_2 _ _ _ h h'); eauto.
    rewrite -> !erase_time; done.
  Qed.

Lemma DBM_Gst_valid_lhst_strong_ext
        (gs : Gst) (i : nat) (s : gset apply_event) (e e' : apply_event):
    DBM_Gst_valid gs →
    gs.(Gst_hst) !! i = Some s →
    e ∈ s → e' ∈ s → ae_time e = ae_time e' → e = e'.
  Proof.
    intros Hgv ? He He' ?.
    eapply DBM_LHV_ext; eauto.
    eapply DBM_GV_hst_lst_valid; eauto.
  Qed.

  Lemma DBM_Gst_valid_ae_provenance (gs : Gst) (i : nat) (s : gset apply_event)
        (e : apply_event) :
    DBM_Gst_valid gs → gs.(Gst_hst) !! i = Some s → e ∈ s →
    ∃ (h : gset write_event), gs.(Gst_mem) !! e.(ae_key) = Some h ∧ erase e ∈ h.
  Proof.
    intros; eapply DBM_GV_hst_in_mem; eauto using elem_of_list_lookup_2.
  Qed.

  Lemma DBM_Gst_valid_causality
        (gs : Gst) (i : nat) (s : gset apply_event) (k : Key)
        (h: gset write_event) (e : apply_event) (a : write_event) :
    DBM_Gst_valid gs →
    gs.(Gst_mem) !! k = Some h → gs.(Gst_hst) !! i = Some s →
    a ∈ h → e ∈ s → vector_clock_lt (we_time a) (ae_time e) →
    ∃ e', e' ∈ (restrict_key k s) ∧ erase e' = a.
  Proof.
    intros Hvg Hkh His Hah Hes Hae.
    pose proof (DBM_GV_mem_elements_key Hvg k h a Hkh Hah) as ->.
    assert (∃ p,  0 < p ∧ a.(we_time) !! a.(we_orig) = Some p)
      as (p & H0p & Harp).
    { by eapply we_in_valid_gs_time. }
    assert (∃ q, p <= q ∧ e.(ae_time) !! a.(we_orig) = Some q)
      as (q & Hpq & Herq).
    { pose proof (vector_clock_lt_le a.(we_time) e.(ae_time) Hae) as Hle.
      eapply Forall2_lookup_l in Hle as (q & Her & Hpq); eauto. }
    edestruct (DBM_lsec_causality_lemma i s e p q) as (e' & He'rs & He'rp);
      eauto using we_in_valid_gs_orig.
    { by eapply DBM_GV_hst_lst_valid. }
    assert (ae_orig e' = we_orig a) as He'_orig.
    { by apply elem_of_filter in He'rs as (Horig&_). }
    assert (∃ h', gs.(Gst_mem) !! e'.(ae_key) = Some h' ∧ erase e' ∈ h')
      as (h' & Hh' & He'h').
    { eapply DBM_GV_hst_in_mem; last eapply in_lsec_in_lhst; eauto.
      eapply elem_of_list_lookup_2; eauto. }
    assert (erase e' = a) as He'a.
    { eapply (DBM_Gst_valid_gmem_ext_internal
                gs (ae_key e') (we_key a) h' h (erase e') a); try done.
      - rewrite -He'_orig. by apply erase_orig.
      - rewrite !erase_time !erase_orig.
          by rewrite !He'_orig Harp He'rp. }
    exists e'; split; last done.
    rewrite elem_of_filter; split; last by eapply in_lsec_in_lhst.
      by rewrite /= -erase_key He'a.
  Qed.

  Global Instance db_states : DB_global_state_valid :=
    {|
    DBM_GstValid gs := DBM_Gst_valid gs;
    DBM_GstValid_empty := DBM_Gst_valid_empty;
    DBM_GstValid_dom gs Hvg := Hvg.(DBM_GV_dom);
    DBM_GstValid_lhst_size gs Hvg:= Hvg.(DBM_GV_hst_size);
    DBM_GstValid_gmem_ext := DBM_Gst_valid_gmem_ext;
    DBM_GstValid_lhst_ext := DBM_Gst_valid_lhst_ext;
    DBM_GstValid_lhst_strong_ext := DBM_Gst_valid_lhst_strong_ext;
    DBM_GstValid_ae_provenance := DBM_Gst_valid_ae_provenance;
    DBM_GstValid_causality := DBM_Gst_valid_causality  |}.

End Global_state_valid.
