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
     Require Import user_params mt_server_code.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code model.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import
     ras
     log_resources
     resources_def
     resources_global_inv
     resources_local_inv.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import
     log_proof
     repdb_serialization.
From aneris.examples.reliable_communication.lib.repdb.proof.leader
     Require Import
     followers_mt_user_params.
From aneris.examples.reliable_communication.lib.repdb.proof.follower
     Require Import
     clients_at_follower_mt_user_params
     proof_of_clients_handler
     proof_of_sync_loop.

Section Init_Follower_Proof.
  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (f2lsa f2csa : socket_address).
  Context (γL γM : gname) (N : gmap socket_address gname).
  Context (follower_si leaderF_si : message → iProp Σ).
  Context (InitFollower : iProp Σ).
  Notation MTC := (client_handler_at_follower_user_params γL γM N f2csa).
  Notation MTF := (follower_handler_user_params γL γM N).
  Context (γF : gname).

  Definition init_follower_res : iProp Σ :=
    Global_Inv γL γM N ∗
    own_log_auth γF (1/2) [] ∗
    own_logL_obs γL [] ∗
    InitFollower ∗
    known_replog_token f2csa γF ∗
    (∃ γdbF : gname, known_replog_token DB_addrF γdbF ∗ own_replog_obs γL DB_addrF []).

  Definition init_follower_spec_internal {MTS:MTS_resources} : iProp Σ :=
    ⌜ip_of_address f2csa = ip_of_address f2lsa⌝ →
    ⌜port_of_address f2csa ≠ port_of_address f2lsa⌝ →
    {{{ unfixed {[f2lsa]} ∗
        f2csa ⤇ follower_si ∗
        DB_addrF ⤇ leaderF_si ∗
        (@run_server_spec _ _ _ _ MTC InitFollower follower_si) ∗
        (@init_client_proxy_spec _ _ _ _ MTF _ leaderF_si) ∗
        (@make_request_spec _ _ _ _ MTF _) ∗
        init_follower_res ∗
        f2csa ⤳ (∅, ∅) ∗
        f2lsa ⤳ (∅, ∅) ∗
        free_ports (ip_of_address f2csa) {[port_of_address f2csa]} ∗
        free_ports (ip_of_address f2lsa) {[port_of_address f2lsa]} }}}
      init_follower (s_serializer DB_serialization)
      #DB_addrF #f2lsa #f2csa @[ip_of_address f2csa]
    {{{ RET #(); True }}}.

  Lemma init_follower_spec_internal_holds {MTR:MTS_resources} :
    ⊢ init_follower_spec_internal.
  Proof.
    iIntros (HipEq HprNeq) "!# %Φ Hr HΦ".
    iDestruct "Hr" as
      "(HA & #Hsi & HsiF & HInitFollowerSpec
            & HinitFollowerAsClient & #HreqSpec
            & HinitRes & Hmh & HmhF & Hfp & HfpF)".
    rewrite /init_follower.
    wp_pures.
    wp_apply (wp_map_empty with "[//]").
    iIntros (kvsV HkvsV).
    wp_alloc kvsL as "HpKvs".
    wp_pures.
    wp_apply (wp_log_create with "[//]").
    iIntros (logL logV) "(HpL & %HlogV)".
    wp_pures.
    iDestruct "HinitRes"
      as "(#HGinv & HownF & #HobsL & Hinit & #HFtkn & #HdbF)".
    iDestruct (get_obs with "[$HownF]") as "#HobsF".
    rewrite - {1} Qp_quarter_quarter.
    iDestruct (own_log_auth_split _ (1/4) (1/4) with "[$HownF]")
      as "(HownF1 & HownF2)".
    wp_apply (new_monitor_spec
                (DB_InvName.@socket_address_to_str f2csa) (ip_of_address f2csa)
                (log_monitor_inv_def
                   (ip_of_address f2csa) γF (1/4) logL
                   (follower_local_res γL kvsL f2csa γF))
               with "[HownF1 HpL HpKvs]") .
    { iFrame "HFtkn".
      iExists logV, [].
      iSplit; first done.
      iFrame.
      iExists kvsV,  ∅.
      iSplit; first done.
      iSplit.
      { iPureIntro. apply valid_state_local_empty. }
      iFrame "#∗". }
    iIntros (mγ mv) "#HLInv".
    wp_let.
    wp_bind (sync_with_server _ _ _ _ _ _).
    rewrite /sync_with_server.
    wp_pures.
    rewrite {4} HipEq.
    wp_apply ("HinitFollowerAsClient" $! f2lsa with "[$HA $HmhF $HfpF $HsiF //]").
    iIntros (reqh) "Hreq".
    wp_pures.
    wp_apply aneris_wp_fork.
    iSplitL "HInitFollowerSpec Hinit Hmh Hfp HΦ".
    - iNext.
      wp_pures.
      rewrite /start_follower_processing_clients.
      wp_pures.
      wp_apply ("HInitFollowerSpec" with "[] [-HΦ]"); [|by iFrame "#∗"|done].
      iIntros (v1 v2 Ψ) "!> HP HΨ".
      wp_pures.
      iApply (client_request_handler_at_follower_spec with "[HLInv $HP]"); [|done].
      Local Transparent monitor_inv is_monitor.
      rewrite /is_monitor /is_lock.
      iDestruct "HLInv" as (lk ->) "HLInv".
      iDestruct "HLInv" as (l ->) "HLInv".
      iExists #l. iSplit; first done.
      iExists l. iSplit; first done.
      iApply (inv_iff with "[$HLInv]").
      iNext. iModIntro.
      rewrite /lock_inv.
      iSplit.
      + iIntros "(%b & (Hl & Hdef))".
        iExists b. iFrame.
        destruct b; first done.
        iDestruct "Hdef" as "(Hk & Hdef)".
        iSplitL "Hk"; first done.
        iSplit; done.
      + iIntros "(%b & (Hl & Hdef))".
        iExists b. iFrame.
        destruct b; first done.
        iDestruct "Hdef" as "(Hk & _ & Hdef)".
        by iFrame.
    - iNext.
      rewrite -HipEq.
      iApply (sync_loop_spec γL γM N f2csa kvsL logL mγ mv _ [] 0
                 with "[HownF2 Hreq] []"); [naive_solver| | done].
      iFrame "HGinv".
      iSplitR; last first.
      { iSplit; [done|].
        iSplitL "Hreq".
        { iExists f2csa. by iFrame. }
        iFrame "#"; eauto.
        iExists _; iFrame "#∗".
        iDestruct "HdbF" as (γdbF) "#(Htk & HobsdbF)".
        iDestruct "HobsdbF" as (γdbF') "(Htk' & _ & HobsdF)".
        iDestruct (known_replog_token_agree with "[$Htk][$Htk']") as "->".
        eauto. }
      rewrite /follower_local_inv.
      iExists γF.
      iFrame "#".
  Qed.

End Init_Follower_Proof.
