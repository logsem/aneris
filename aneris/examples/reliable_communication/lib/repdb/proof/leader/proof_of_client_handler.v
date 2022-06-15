From iris.algebra Require Import agree auth excl gmap dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From aneris.examples.reliable_communication.lib.mt_server Require Import user_params.
From aneris.examples.reliable_communication.lib.repdb Require Import repdb_code model.
From aneris.examples.reliable_communication.lib.repdb.spec Require Import db_params events.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import ras log_resources resources_def
     resources_global_inv resources_local_inv.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import repdb_serialization.
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
    rewrite /ReqPre.
    iDestruct "Hpre" as "(#HGinv & [HpreW | HpreR])".
    - admit.
    - iDestruct "HpreR" as (k we q Hkeys Hreqd ->) "Hk".
      wp_pures.
      iDestruct "HR" as (lV lM) "(%Hlog & Hpl & HlogL & HR)".
      iDestruct "HR" as (kvsV kvsM) "(%Hkvs & %HvalidLocal & Hpm)".
      wp_load.
      wp_apply (wp_map_lookup $! Hkvs).
      iIntros (v Hv).
      inversion HvalidLocal.
      wp_apply fupd_aneris_wp.
      iMod (OwnMemKey_wo_obs_holds with "HGinv Hk")
        as "(Hk & (%lM' & #HObsL & <-))"; [solve_ndisj|].
      iDestruct (own_obs_prefix _ _ lM lM' with "[$HlogL][HObsL]") as "%Hprefix".
      by iApply Obs_own_log_obs.
      iDestruct (get_obs with "[$HlogL]") as "#HObsL'".
      iMod (OwnMemKey_obs_frame_prefix_holds
             with "[$HGinv][Hk HObsL]") as "(Hk & %Heq)";
        [solve_ndisj|done|iFrame "#∗"; by iLeft|].
      iAssert ( |={⊤}=> ( ⌜v = InjLV #()⌝ ∗ ⌜at_key k lM' = None⌝) ∨
              (∃ a : write_event,
                  ⌜v = (InjRV (we_val a))⌝ ∗ ⌜at_key k lM' = Some a⌝))%I
        as ">Hpost".
      { destruct (kvsM !! k) eqn:Hmk; rewrite Hmk in Hv; rewrite Hv.
        - iModIntro. iRight.
          apply DB_LSTV_in_mem_log_some_coh_local in Hmk;
            last by apply elem_of_dom.
          destruct Hmk as (we0 & Hwe0L & <-).
          iExists _. iSplit; first done. iPureIntro. by rewrite Heq.
        - iModIntro.
          iLeft.
          iSplit; first done.
          iPureIntro.
          apply DB_LSTV_in_mem_log_none_coh_local in Hmk.
          by rewrite Heq. }
      iModIntro.
      wp_pures.
      destruct (kvsM !! k) eqn:Hmk; rewrite Hmk in Hv; rewrite Hv.
      -- iDestruct "Hpost" as "[(%Habs & _)|Hpost]"; first done.
         iDestruct "Hpost" as (a Ha) "%Hwe".
         iApply ("HΦ" $! _ (inr (Some a))).
         iFrame "Hkey".
         iSplit.
         { iPureIntro.
           assert (k ∈ dom kvsM) as Hk by by apply elem_of_dom.
           assert (v0 = (we_val a)) as -> by naive_solver.
           specialize (DB_LSTV_mem_serializable_vs_local k (we_val a) Hk Hmk).
           apply _. }
         simpl.
         rewrite /log_monitor_inv_def /ReqPost.
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
         { rewrite /rep_l2c_serialization.
           iPureIntro.
           apply _. }
         simpl.
         rewrite /log_monitor_inv_def /ReqPost.
         iSplitR "Hk"; last first.
         { iRight.
           iExists _, _, _.
           iSplit; first done.
           iExists v.
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
  Admitted.

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
