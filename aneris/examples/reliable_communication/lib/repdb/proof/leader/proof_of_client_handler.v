From iris.algebra Require Import agree auth excl gmap dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.prelude
     Require Import ser_inj.
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code model.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events stdpp_utils.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import ras log_resources resources_def
     resources_global_inv resources_local_inv.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import repdb_serialization log_proof.
From aneris.examples.reliable_communication.lib.repdb.proof.leader
     Require Import clients_mt_user_params.

Import gen_heap_light.

Section Clients_MT_spec_params.

  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (γL γM : gname) (N : gmap socket_address gname).
  Context (mγ : gname) (mv : val) (kvsL logL : loc).

  Notation MTU := (client_handler_at_leader_user_params γL γM N).

  Lemma client_request_handler_at_leader_spec  :
    ∀ reqv reqd,
    {{{ leader_local_main_inv γL kvsL logL mγ mv ∗
        MTU.(MTS_handler_pre) reqv reqd }}}
        client_request_handler_at_leader #kvsL #logL mv reqv  @[ip_of_address MTU.(MTS_saddr)]
    {{{ repv repd, RET repv;
        ⌜Serializable (rep_l2c_serialization) repv⌝ ∗
         MTU.(MTS_handler_post) repv reqd repd }}}.
  Proof.
    iIntros (reqv reqd Φ) "(#Hmon & Hpre) HΦ".
    rewrite /client_request_handler_at_leader.
    wp_pures.
    wp_apply (monitor_acquire_spec with "[Hmon]"); first by iFrame "#".
    iIntros (v) "(-> & HKey & HR)".
    iDestruct "HR" as (lV lM) "(%Hlog & Hpl & HlogL & HR)".
    iDestruct "HR" as (kvsV kvsM) "(%Hkvs & %HvalidLocal & Hpm)".
    iDestruct "Hpre" as "((#Htks & #HGinv) & [HpreW | HpreR])".
    do 2 wp_pure _.
    - iDestruct "HpreW" as (E k v P Q) "(%Hrd & -> & %HE & %Hkeys & P & Hvsh)".
      wp_pures.
      wp_load.
      wp_apply (wp_map_insert $! Hkvs).
      iIntros (m' Hm').
      wp_bind (Store _ _).
      wp_apply (aneris_wp_atomic _ _ E).
      set (a := {|we_key := k; we_val := v;
                               we_time := (length lM : int_time.(Time))|}).
      iMod ("Hvsh" with "[$P]") as (h a_old) "(%Hkh & Hk & Hobsh & Hpost)".
      iDestruct (own_obs_prefix with "[$HlogL][Hobsh]") as "%Hprefixh".
      { by iApply Obs_own_log_obs. }
      rewrite -{1} Hkh.
      iDestruct (get_obs with "[$HlogL]") as "#HobsL".
      iMod (OwnMemKey_obs_frame_prefix_holds _ _ _ DB_addr
                   with "[$ Htks $HGinv][$Hk $HobsL]") as "(Hk & %Heqhk)";
        [solve_ndisj|apply Hprefixh | by iLeft | ].
      destruct Hprefixh as (hf & Hprefixh).
      assert (at_key k hf = None) as Hnone.
      { apply (at_key_app_none _ h).
        - rewrite -Hprefixh.
          by eapply valid_state_local_log_no_dup.
        - naive_solver. }
      iInv DB_InvName
        as (lMG kvsMG) ">(%HkG & %Hdom & %Hdisj & HmS & HlM & HknwF & HmapF & %HvalidG)".
      iDestruct (own_log_auth_combine with "HlM HlogL") as "(HlFull & ->)".
      rewrite Qp.half_half.
      iDestruct (own_obs_prefix with "[$HlFull][Hobsh]") as "%Hprefixh2".
      by iApply Obs_own_log_obs.
      iMod (own_log_auth_update _ _ (lM ++ [a]) with "[$HlFull]") as "HlFull".
      { by apply prefix_app_r. }
      iMod (own_mem_update _ _ _ _ a with "[$Hk][$HmS]") as "(Hk & HmS)".
      rewrite - {4} Qp.half_half.
      iDestruct (own_log_auth_split with "HlFull") as "(HlogM & HlogL)".
      iDestruct (get_obs with "[$HlogL]") as "#Hobsfr2".
      iModIntro. rewrite /global_inv_def. iSplitL "HlogM HmS HmapF HknwF".
      { iNext.
        iExists _, _.
        iFrame.
        erewrite dom_insert_L, DB_GSTV_mem_dom; last done.
        iPureIntro.
        split; first set_solver.
        do 2 (split; first done).
        apply valid_state_update; eauto; apply _. }
      iDestruct ("Hpost" $! hf a with "[//][//][//][][$Hk][Hobsfr2]") as "HQ".
      { iPureIntro. inversion HvalidLocal. iIntros (e He).
        assert (e ∈ lM) as HelM. { set_solver. }
        assert (e.(we_time) < length lM) as Htime.
        { destruct (elem_of_list_lookup_1 lM e HelM) as [n Hnth].
          assert (n < length lM)%nat as Hnh.
          { apply lookup_lt_is_Some_1; eauto. }
          destruct (DB_LSTV_log_events n Hnh) as (e' & He' & He'time & He'keys).
          assert (e = e') as Heqe. { rewrite Hnth in He'. by inversion He'. }
          rewrite Heqe - He'time. lia. }
        done. }
      { iNext. iLeft. list_simplifier. iSplit; first done. iFrame "#". }
      { iModIntro.
        wp_store.
        iMod "HQ".
        iModIntro.
        wp_pures.
        wp_apply (wp_log_length with "[$Hpl]"); [done|].
        iIntros (n) "(%Hlen & _ & Hpl)".  wp_pures.
        rewrite Hlen.
        wp_apply (wp_log_add_entry _ _ _ lM a with "[$Hpl]"); [done|].
        iIntros (logV') "(%Hlog' & Hpl')". wp_pures.
        rewrite /leader_local_main_inv /log_monitor_inv.
        wp_smart_apply (monitor_signal_spec _ mγ with "[$HKey $Hmon Hpm Hpl' HlogL]").
        { iExists _, _. iFrame "#∗". iSplit; first done. iExists _. iFrame.
          iExists _. iSplit; first done. iPureIntro.
          apply valid_state_local_update; try eauto. apply _. }
        iIntros "(Hkey & HlRes)".
        wp_pures.
        wp_apply (monitor_release_spec with "[$Hmon $HlRes $Hkey]").
        iIntros (v' ->).
        do 2 wp_pure _.
        iApply "HΦ".
        iSplit; [iPureIntro; apply _ |]. simpl; rewrite /ReqPost.
        iFrame.
        iLeft.
        iExists _, _, _, _, _.
        iSplit; first done.
        eauto with iFrame. }
    - iDestruct "HpreR" as (k we q Hkeys Hreqd ->) "Hk".
      wp_pures.
      wp_load.
      wp_apply (wp_map_lookup $! Hkvs).
      iIntros (v Hv).
      inversion HvalidLocal.
      wp_apply fupd_aneris_wp.
      iAssert (Global_Inv γL γM N) as "#HGinvR". { by iFrame "#". }
      iMod (OwnMemKey_wo_obs_holds with "HGinvR Hk")
        as "(Hk & (%lM' & #HObsL & <-))"; [solve_ndisj|].
      iDestruct (own_obs_prefix _ _ lM lM' with "[$HlogL][HObsL]")
        as "%Hprefix". by iApply Obs_own_log_obs.
      iDestruct (get_obs with "[$HlogL]") as "#HObsL'".
      iMod (OwnMemKey_obs_frame_prefix_holds
             with "[$HGinvR][Hk HObsL]") as "(Hk & %Heq)";
        [solve_ndisj|done|iFrame "#∗"; by iLeft|].
      iAssert (|={⊤}=>
                 (⌜v = InjLV #()⌝ ∗ ⌜at_key k lM' = None⌝) ∨
                   (∃ a : write_event,
                       ⌜v = (InjRV (we_val a))⌝ ∗ ⌜at_key k lM' = Some a⌝))%I
        as ">Hpost".
      { destruct (kvsM !! k) eqn:Hmk; rewrite Hmk in Hv; rewrite Hv.
        - iModIntro. iRight.
          apply DB_LSTV_in_mem_log_some_coh_local in Hmk.
          destruct Hmk as (we0 & Hwe0L & <-).
          iExists _.
          iSplit; first done.
          iPureIntro.
          by rewrite Heq.
        - iModIntro.
          iLeft. iSplit; first done.
          iPureIntro.
          apply DB_LSTV_in_mem_log_none_coh_local in Hmk.
          by rewrite Heq. }
      iModIntro. wp_pures.
      destruct (kvsM !! k) eqn:Hmk; rewrite Hmk in Hv; rewrite Hv.
      -- iDestruct "Hpost" as "[(%Habs & _)|Hpost]"; first done.
         iDestruct "Hpost" as (a Ha) "%Hwe".
         wp_apply (monitor_release_spec with "[$Hmon HlogL Hpl Hpm $HKey]").
         { iExists _, _. iFrame "#∗". iSplit; first done.
           iExists _, _. eauto with iFrame. }
         iIntros (v' ->).
         do 2 wp_pure _.
         iApply ("HΦ" $! _ (inr (Some a))). iSplit.
         { iPureIntro.
           assert (k ∈ dom kvsM) as Hk by by apply elem_of_dom.
           assert (v0 = (we_val a)) as -> by naive_solver.
           specialize (DB_LSTV_mem_serializable_vs_local k (we_val a) Hmk).
           apply _. }
         simpl. rewrite /log_monitor_inv_def /ReqPost.
         { iRight.
           iExists k, (Some a), q.
           rewrite Hwe in Hreqd.
           iSplit; first done.
           iExists ((InjRV v0)).
           do 2 (iSplit; first done).
           rewrite Hwe.
           iFrame.
           iRight.
           by iExists _. }
      -- wp_apply (monitor_release_spec with "[$Hmon HlogL Hpl Hpm $HKey]").
         { iExists _, _. iFrame "#∗". iSplit; first done.
           iExists _, _. eauto with iFrame. }
         iIntros (v' ->).
         do 2 wp_pure _.
         iApply ("HΦ" $! _ (inr None)).
         iDestruct "Hpost" as "[(_ & ->) |%Habs]"; [|naive_solver].
         iSplit.
         { rewrite /rep_l2c_serialization. iPureIntro. apply _. }
         simpl. rewrite /log_monitor_inv_def /ReqPost.
         { iRight. iExists _, _, _. iSplit; first done. iExists v.
           apply DB_LSTV_in_mem_log_none_coh_local in Hmk.
           rewrite -Hmk Heq Hv.
           do 2 (iSplit; first done).
           iFrame.
           by iLeft. }
  Qed.

End Clients_MT_spec_params.
