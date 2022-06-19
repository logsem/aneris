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
Import lock_proof.

Section Clients_MT_spec_params.

  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (γL γM : gname).
  Context (mγ : gname) (mv : val) (kvsL logL : loc).

  Definition handler_cloj : val :=
    λ: "mon" "req", client_request_handler_at_leader #kvsL #logL "mon" "req".

  Notation MTU := (client_handler_at_leader_user_params γL γM).

  Lemma client_request_handler_at_leader_spec  :
    ∀ reqv reqd,
    {{{ leader_local_main_inv γL kvsL logL mγ mv ∗
        lock_proof.locked mγ ∗
        (log_monitor_inv_def
           (ip_of_address MTU.(MTS_saddr)) γL (1/2) logL
           (leader_local_main_res kvsL)) ∗
           MTU.(MTS_handler_pre) reqv reqd }}}
       handler_cloj mv reqv @[ip_of_address MTU.(MTS_saddr)]
    {{{ repv repd, RET repv;
        ⌜Serializable (rep_l2c_serialization) repv⌝ ∗
        lock_proof.locked mγ ∗
          (log_monitor_inv_def
             (ip_of_address MTU.(MTS_saddr)) γL (1/2) logL
             (leader_local_main_res kvsL)) ∗
          MTU.(MTS_handler_post) repv reqd repd }}}.
  Proof.
    iIntros (reqv reqd Φ) "(#Hmon & Hkey & HR & Hpre) HΦ".
    rewrite /handler_cloj /client_request_handler_at_leader.
    wp_pures.
    iDestruct "HR" as (lV lM) "(%Hlog & Hpl & HlogL & HR)".
    iDestruct "HR" as (kvsV kvsM) "(%Hkvs & %HvalidLocal & Hpm)".
    iDestruct "Hpre" as "(#HGinv & [HpreW | HpreR])".
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
      iMod (OwnMemKey_obs_frame_prefix_holds _ _ DB_addr
                   with "[$HGinv][$Hk $HobsL]") as "(Hk & %Heqhk)";
        [solve_ndisj|apply Hprefixh | by iLeft | ].
      destruct Hprefixh as (hf & Hprefixh).
      assert (at_key k hf = None) as Hnone.
      { apply (at_key_app_none _ h).
        - rewrite -Hprefixh.
          by eapply valid_state_local_log_no_dup.
        - naive_solver. }
      iInv DB_InvName
        as (lMG kvsMG) ">(%N & %HkG & %Hdom & %Hdisj & HmS & HlM & HknwF & HmapF & %HvalidG)".
      iDestruct (own_log_auth_combine with "HlM HlogL") as "(HlFull & ->)".
      rewrite Qp_half_half.
      iDestruct (own_obs_prefix with "[$HlFull][Hobsh]") as "%Hprefixh2".
      by iApply Obs_own_log_obs.
      iMod (own_log_auth_update _ _ (lM ++ [a]) with "[$HlFull]") as "HlFull".
      { by apply prefix_app_r. }
      iMod (own_mem_update γM _ _ _ _ a with "[$Hk][$HmS]") as "(Hk & HmS)".
      rewrite - {5} Qp_half_half.
      iDestruct (own_log_auth_split with "HlFull") as "(HlogM & HlogL)".
      iDestruct (get_obs with "[$HlogL]") as "#Hobsfr2".
      iModIntro. rewrite /global_inv_def. iSplitL "HlogM HmS HmapF HknwF".
      { iNext.
        iExists _, _, _.
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
        { apply elem_of_list_In in HelM.
          destruct (In_nth_error lM e HelM) as [n Hnth].
          assert (n < length lM) as Hnh.
          { apply (nth_error_Some _ _). by rewrite Hnth. }
          assert  (0 ≤ n)%Z as Hn0Z by lia.
          apply inj_lt in Hnh.
          destruct (DB_LSTV_log_events lM n Hn0Z Hnh) as (e' & He' & He'time & He'keys).
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
        wp_apply (monitor_signal_spec with "[$Hkey $Hmon Hpm Hpl' HlogL]").
        { iExists _, _. iFrame "#∗". iSplit; first done. iExists _. iFrame.
          iExists _. iSplit; first done. iPureIntro.
          apply valid_state_local_update; try eauto. apply _. }
        iIntros "(Hkey & HlRes)".
        wp_pures.
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
      iMod (OwnMemKey_wo_obs_holds with "HGinv Hk")
        as "(Hk & (%lM' & #HObsL & <-))"; [solve_ndisj|].
      iDestruct (own_obs_prefix _ _ lM lM' with "[$HlogL][HObsL]")
        as "%Hprefix". by iApply Obs_own_log_obs.
      iDestruct (get_obs with "[$HlogL]") as "#HObsL'".
      iMod (OwnMemKey_obs_frame_prefix_holds
             with "[$HGinv][Hk HObsL]") as "(Hk & %Heq)";
        [solve_ndisj|done|iFrame "#∗"; by iLeft|].
      iAssert (|={⊤}=>
                 (⌜v = InjLV #()⌝ ∗ ⌜at_key k lM' = None⌝) ∨
                   (∃ a : write_event,
                       ⌜v = (InjRV (we_val a))⌝ ∗ ⌜at_key k lM' = Some a⌝))%I
        as ">Hpost".
      { destruct (kvsM !! k) eqn:Hmk; rewrite Hmk in Hv; rewrite Hv.
        - iModIntro. iRight.
          apply DB_LSTV_in_mem_log_some_coh_local in Hmk;
            last by apply elem_of_dom.
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
         iApply ("HΦ" $! _ (inr (Some a))). iFrame "Hkey". iSplit.
         { iPureIntro.
           assert (k ∈ dom kvsM) as Hk by by apply elem_of_dom.
           assert (v0 = (we_val a)) as -> by naive_solver.
           specialize (DB_LSTV_mem_serializable_vs_local k (we_val a) Hk Hmk).
           apply _. }
         simpl. rewrite /log_monitor_inv_def /ReqPost.
         iSplitR "Hk"; last first.
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
         iExists _, _.
         iSplit; first done.
         iFrame.
         iExists _, _.
         by iFrame.
      -- iApply ("HΦ" $! _ (inr None)).
         iDestruct "Hpost" as "[(_ & ->) |%Habs]"; [|naive_solver].
         iFrame "Hkey".
         iSplit.
         { rewrite /rep_l2c_serialization. iPureIntro. apply _. }
         simpl. rewrite /log_monitor_inv_def /ReqPost.
         iSplitR "Hk"; last first.
         { iRight. iExists _, _, _. iSplit; first done. iExists v.
           apply DB_LSTV_in_mem_log_none_coh_local in Hmk.
           rewrite -Hmk Heq Hv.
           do 2 (iSplit; first done).
           iFrame.
           by iLeft. }
         iExists _, _.
         iSplit; first done.
         iFrame.
         iExists _, _.
         by iFrame.
  Qed.

  Global Instance client_handler_at_leader_spec_params :
    @MTS_spec_params _ _ _ _ MTU :=
    {|
      MTS_mR := (log_monitor_inv_def
                   (ip_of_address MTU.(MTS_saddr)) γL (1/2) logL
                   (leader_local_main_res kvsL));
      MTS_mγ := mγ;
      MTS_mv := mv;
      MTS_handler := handler_cloj;
      MTS_handler_spec := client_request_handler_at_leader_spec;
    |}.

End Clients_MT_spec_params.
