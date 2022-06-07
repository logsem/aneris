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
     clients_mt_user_params
     followers_mt_user_params
     proof_of_client_handler
     proof_of_followers_handler
     proof_of_update_log_copy_loop.

Section Init_Leader_Proof.
  Context `{aG : !anerisG Mdl Σ, dbparams : !DB_params, dbg: !IDBG Σ}.
  Context (γL γM γF : gname).
  Context (leader_si leaderF_si : message → iProp Σ).
  Context (SrvLeaderInit SrvLeaderFInit : iProp Σ).
  Notation MTC := (client_handler_at_leader_user_params γL γM).
  Notation MTF := (follower_handler_user_params γL γM).
  Context (HInitLeaderSpec :
          ⊢  (∀ (MTS : MTS_spec_params MTC) A,
                @run_server_spec _ _ _ _ _ SrvLeaderInit leader_si MTS A)).
  Context (HInitLeaderFSpec :
          ⊢  (∀ (MTS : MTS_spec_params MTF) A,
                @run_server_spec _ _ _ _ _ SrvLeaderFInit leaderF_si MTS A)).

  Definition init_leader_res : iProp Σ :=
    Global_Inv γL γM ∗
    own_log_auth γL (1/2) [] ∗
    SrvLeaderInit ∗
    known_replog_token DB_addrF γF ∗
    own_log_auth γF (1/2) [] ∗
    SrvLeaderFInit.

  Definition init_leader_spec_internal A : iProp Σ :=
    ⌜DB_addr ∈ A⌝ →
    ⌜DB_addrF ∈ A⌝ →
    ⌜ip_of_address DB_addrF = ip_of_address DB_addr⌝ →
    ⌜port_of_address DB_addrF ≠ port_of_address DB_addr⌝ →
    {{{ fixed A ∗
          DB_addr ⤇ leader_si ∗
          DB_addrF ⤇ leaderF_si ∗
          init_leader_res ∗
          DB_addr ⤳ (∅, ∅) ∗
          DB_addrF ⤳ (∅, ∅) ∗
          free_ports (ip_of_address DB_addr) {[port_of_address DB_addr]} ∗
          free_ports (ip_of_address DB_addrF) {[port_of_address DB_addrF]} }}}
      init_leader (s_serializer DB_serialization)
      #DB_addr #DB_addrF @[ip_of_address DB_addr]
    {{{ RET #(); True }}}.

  Lemma init_leader_spec_internal_holds A : ⊢ init_leader_spec_internal A.
  Proof.
    iIntros (HinA HinFA HipEq HprNeq) "!# %Φ Hr HΦ".
    iDestruct "Hr" as
      "(#HA & #Hsi & #HsiF & HinitRes & Hmh & HmhF & Hfp & HfpF)".
    rewrite /init_leader.
    wp_pures.
    wp_apply (wp_log_create with "[//]").
    iIntros (logL logV) "(HpL & %HlogV)".
    wp_pures.
    wp_apply (wp_log_create with "[//]").
    iIntros (logLF logVF) "(HpLF & %HlogVF)".
    wp_pures.
    wp_apply (wp_map_empty with "[//]").
    iIntros (kvsV HkvsV).
    wp_alloc kvsL as "HpKvs".
    wp_pures.
    iDestruct "HinitRes"
      as "(#HGinv & HownL & HsrvInit & #HFtkn & HownF & HsrvFinit)".
    iDestruct (get_obs with "[$HownL]") as "#HobsL".
    rewrite -Qp_quarter_quarter.
    rewrite {1} Qp_quarter_quarter.
    iDestruct (own_log_auth_split _ (1/4) (1/4) with "[$HownF]")
      as "(HownF1 & HownF2)".
    wp_apply (new_monitor_spec
                (DB_InvName .@ "leader_main") (ip_of_address DB_addr)
                (log_monitor_inv_def
                   (ip_of_address DB_addr) γL (1/2) logL
                   (leader_local_main_res kvsL))
               with "[HownL HpL HpKvs]") .
    iExists logV, [].
    iSplit; first done.
    iFrame.
    iExists kvsV,  ∅.
    iSplit; first done.
    iSplit.
    { iPureIntro. apply valid_state_local_empty. }
    iFrame.
    iIntros (mγ mv) "#HLInv".
    wp_pures.
    symmetry in HipEq.
    rewrite {4 5} HipEq.
    wp_apply (new_monitor_spec
                (DB_InvName .@ "leader_secondary") (ip_of_address DB_addrF)
                (log_monitor_inv_def
                   (ip_of_address DB_addrF) γF (1/4) logLF
                   (leader_local_secondary_res γL γF))
               with "[HownF1 HpLF HFtkn HobsL]") .
    iExists logVF, [].
    iSplit; first done.
    iFrame "#∗".
    iIntros (mFγ mFv) "#HLFInv".
    wp_pures.
    wp_apply aneris_wp_fork.
    iSplitR "HsrvInit Hmh Hfp".
    - iNext.
      wp_pures.
      wp_apply aneris_wp_fork.
      iSplitR "HsrvFinit HmhF HfpF".
      -- iNext.
         wp_pures.
         wp_apply aneris_wp_fork.
         iSplitL "HΦ"; iNext; [ by iApply "HΦ"|].
         rewrite -HipEq.
         wp_apply (update_log_copy_loop_spec γL γM  _ γF mFγ
                    with "[HownF2]"); [ | done].
         iFrame "#∗".
         rewrite /leader_local_secondary_inv.
         rewrite /log_monitor_inv.
         by rewrite HipEq.
         Unshelve. done.
      -- rewrite /start_leader_processing_followers.
         iNext.
         wp_pures.
         wp_apply
           (HInitLeaderFSpec $! (follower_handler_spec_params
                                   γL γM mFγ γF mFv logLF) A _
             with "[$HsrvFinit $HmhF $HfpF]"); eauto with iFrame.
    - rewrite /start_leader_processing_clients.
      iNext.
      wp_pures.
      rewrite -HipEq.
      wp_apply
        (HInitLeaderSpec $! (client_handler_at_leader_spec_params
                               γL γM mγ mv kvsL logL) A _
          with "[$HsrvInit $Hmh $Hfp]"); eauto with iFrame.
  Qed.

End Init_Leader_Proof.
