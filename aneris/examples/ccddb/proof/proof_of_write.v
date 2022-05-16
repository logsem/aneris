(** Proof the causal memory implementation w.r.t. modular specification. *)
From iris.algebra Require Import agree auth excl gmap.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import lang network tactics proofmode lifting.
From aneris.aneris_lang.lib Require Import list_proof map_proof lock_proof network_util_proof inject.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb Require Import ccddb_code.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import
     model_lst model_gst model_update_system model_update_lst model_update_gst.
From aneris.examples.ccddb.resources Require Import
     base resources_gmem resources_lhst resources_local_inv resources_global_inv.

Import ast.

Section proof.
  Context `{!anerisG Mdl Σ, !DB_params, !internal_DBG Σ}.
  Context (γGauth γGsnap γGkeep : gname) (γLs : list (gname * gname)).

  Definition internal_write_spec
             (wr : val) (i: nat) (z : socket_address) : iProp Σ :=
    Eval simpl in
    □ (∀ (E : coPset) (k : Key) (v : SerializableVal) (s: gset apply_event)
         (P : iProp Σ)
         (Q : apply_event → gset write_event → gset apply_event → iProp Σ),
        ⌜DB_addresses !! i = Some z⌝ -∗
        ⌜↑DB_InvName ⊆ E⌝ -∗
        □ (∀ (s1: gset apply_event) (e: apply_event),
            let s' := s1 ∪ {[ e ]} in
            ⌜s ⊆ s1⌝ → ⌜e ∉ s1⌝ →
            ⌜e.(ae_key) = k⌝ → ⌜e.(ae_val) = v⌝ →
            P ={⊤, E}=∗
            ∀ (h : gset write_event),
              let a  := erase e in
              let h' := h ∪ {[ a ]} in
              ⌜a ∉ h⌝ →
              ⌜a ∈ compute_maximals we_time h'⌝ →
              ⌜compute_maximum ae_time s' = Some e⌝ →
              local_history_seen γLs i s' -∗
              own_mem_sys γGauth γGsnap γGkeep k h
              ={E∖↑DB_InvName}=∗ own_mem_sys γGauth γGsnap γGkeep k h'
                                ∗ |={E, ⊤}=> Q e h s1) -∗
        {{{ ⌜k ∈ DB_keys⌝ ∗ P ∗ local_history_seen γLs i s }}}
          wr #k v @[ip_of_address z]
        {{{ RET #();
              ∃ (h: gset write_event) (s1: gset apply_event) (e: apply_event),
                ⌜s ⊆ s1⌝ ∗  Q e h s1 }}})%I.

  Lemma internal_write_spec_holds
        (i : nat) (z : socket_address) (DB T IQ OQ : loc) (lk : val)
        (γlk : gname) :
    {{{ Global_Inv γGauth γGsnap γGkeep γLs ∗
        local_invariant γGsnap γLs i DB T IQ OQ lk γlk z }}}
      store_write #DB #T #OQ lk #i @[ip_of_address z]
    {{{ wr, RET wr; internal_write_spec wr i z }}}.
  Proof.
    rewrite /store_write /local_invariant.
    remember (ip_of_address z) as ip.
    iIntros (Φ) "(#Ginv & #Linv) HΦ".
    wp_pures. iApply "HΦ". rewrite /internal_write_spec.
    rewrite -Heqip.
    iModIntro.
    iIntros (E k v s P Q Hiz HE) "#Hvs".
    clear Φ.
    iIntros (Φ) "!# (Hk & HP & #HS) HΦ".
    iDestruct "Hk" as %Hk.
    wp_pures.
    wp_apply acquire_spec; first iExact "Linv".
    iIntros (?) "(-> & Hlk & Hli)".
    simpl.
    wp_pures.
    wp_bind (! _)%E.
     iDestruct "Hli" as (vd vt viq voq d t liq loq s' ip')
    "(Hip'& HDB & HT & HIQ & HOQ & #Hdict & #Hvc &Hliv &#Hlstv)".
    iDestruct "Hip'" as %Hip'.
    iDestruct "Hlstv" as %Hlstv.
    iDestruct "Hvc" as %Hvc.
    iDestruct "Hdict" as %Hdict.
    rewrite Hiz in Hip'; simpl in Hip'.
    simplify_eq Hip'; intros <-; rewrite -!Heqip.
    wp_load; simpl.
    assert (i < (length t))%nat as Hlit.
    { erewrite (DBM_LSTV_time_length Hlstv);
        eauto using DBM_LSTV_at. }
    destruct (lookup_lt_is_Some_2 _ _ Hlit) as [ti Hti].
    wp_apply (wp_vect_inc); eauto with lia; try lia.
    iIntros (vt' Hvt').
    wp_store. wp_pures.
    wp_load.
    wp_apply (wp_map_insert $! Hdict).
    iIntros (w Hw); simpl.
    wp_store.
    wp_pures.
    iApply fupd_aneris_wp.
    iDestruct (local_history_seen_included with "Hliv HS") as %Hss'.
    set (e := ApplyEvent k v
                  (incr_time t i) i (S (length (elements s')))).
    assert (e ∉ s') as Hes'.
    { by apply (DBM_system_write_event_fresh_lhst e i d t). }
    iMod ("Hvs" $! s' e with "[//] [//] [//] [//] HP") as "Hvs1".
    iInv DB_InvName as
        (M Ss) "(>% & >Hkm & >Ha & >Hs & >Hk1 & >Hk2 & >Hl & >Hvl)".
    iDestruct "Hkm" as %Hkm.
    iDestruct "Hvl" as %Hvl.
    assert (k ∈ dom M) as Hk'.
    { by rewrite Hkm in Hk. }
    apply elem_of_dom in Hk' as [h Hkh].
    iDestruct (local_history_invs_agree with "Hl Hliv") as %His'.
    assert (erase e ∉ h) as Heh.
    { by eapply DBM_system_write_event_fresh_gmem. }
    assert (erase e ∈ compute_maximals we_time (h ∪ {[erase e]})) as Herase_max.
    { eapply DBM_system_write_event_maximals_gmem; eauto. }
    assert (compute_maximum ae_time (s' ∪ {[e]}) = Some e) as Hmax.
    { by eapply DBM_system_write_event_maximum_lhst. }
    assert (DBM_Lst_valid i (LST (<[k:= v : val]> d)
                                 (incr_time t i) ( s' ∪ {[e]})))
      as Hlstv'.
    { eapply (DBM_lst_update_write e i _ Hlstv); eauto. }
    assert ( DBM_GstValid
               {| Gst_mem := <[k:= h  ∪ {[erase e]} ]> M;
                  Gst_hst := <[i:= s' ∪ {[e]}]> Ss |}) as Hvl'.
    { by eapply (DBM_system_write_update_gst k v i _ _ h Hk Hlstv Hvl). }
     iMod (local_history_update _ _ _ _ e with "Hliv Hl") as "[Hl Hliv]".
    { intros e' He' Hlt.
      assert (vector_clock_lt (ae_time e') (ae_time e)) as Hlt'.
      { apply compute_maximum_correct in Hmax as (Hmaxin & Hmaxlt).
        - apply Hmaxlt; set_solver.
        - eapply DBM_LHV_ext.
          eapply (DBM_LSTV_hst_valid Hlstv'). }
        by eapply vector_clock_lt_exclusion. }
    iMod (observe_local_history_internal with "Hs Hl Hliv") as
        "(Hs & Hl & Hliv & Hs'')".
    iMod (create_own_mem_sys_update _ _ _ M k h with "Ha Hs Hk1 Hk2") as
        "[Hsys Hupd]"; [done|done|].
    iMod ("Hvs1" $! h with "[//] [//] [//] Hs'' Hsys") as "[Hsys HQ]".
    iMod ("Hupd" with "Hsys") as "(Ha&Hs&Hk1&Hk2)".
    iDestruct "HOQ" as "(HOQ & Hvoq & Hloq)".
    iDestruct "Hvoq" as %Hvoq.
    iMod (get_snapshot _ _ k with "Hs") as "[Hs Hsnap]";
      first by rewrite lookup_insert.
    iAssert ([∗ list] a ∈ (erase e :: loq),
             ⌜DB_Serializable (we_val a)⌝ ∗
             ⌜we_key a ∈ DB_keys⌝ ∗
             ⌜a.(we_orig) = i⌝ ∗
             own_mem_snapshot γGsnap (we_key a) {[a]})%I
      with "[Hloq Hsnap]" as "Hloq".
    { iSplit; last done.
      rewrite /e /=.
      iSplit; first by iPureIntro; apply _.
      iSplit; first done.
      iSplit; first done.
      iApply (own_mem_snapshot_weaken with "Hsnap"); set_solver. }
    iModIntro.
    iSplitL "Ha Hs Hk1 Hk2 Hl".
    { iNext. iExists _, _; iFrame.
      repeat iSplit; try done.
      - rewrite dom_insert_L subseteq_union_1_L //.
        apply elem_of_subseteq_singleton, elem_of_dom; eauto. }
    iMod "HQ".
    iModIntro.
    wp_load.
    wp_load.
    wp_pures.
    set we := (WriteEvent k v (incr_time t i) i).
    replace (#k, v, vt', #i)%V with ($ we : val); last first.
    { simpl.
      by apply is_vc_vector_clock_to_val in Hvt' as ->. }
    wp_apply wp_list_cons; first done.
    iIntros (voq' (?&->&?)).
    wp_store.
    wp_pures.
    wp_apply (release_spec with "[$Hlk HDB HT HOQ HIQ Hloq Hliv]").
      { iFrame "Linv".
        iExists _, _, _, _, _, _, _, _; iExists _, _.
        iFrame "HIQ"; iFrame; iFrame "#".
        rewrite Hiz /= -Heqip.
        repeat iSplit; eauto.
      }
      iIntros (v0 ->). iApply "HΦ"; eauto with iFrame.
  Qed.

End proof.
