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
From aneris.examples.reliable_communication.lib.repdb.proof.follower
     Require Import
     clients_at_follower_mt_user_params
     proof_of_clients_handler
     proof_of_sync_loop.

Section Init_Follower_Proof.
  Context `{aG : !anerisG Mdl Σ, dbparams : !DB_params, dbg: !IDBG Σ}.
  Context (f2lsa f2csa : socket_address).
  Context (γL γM : gname) (N : gmap socket_address gname).
  Context (follower_si leaderF_si : message → iProp Σ).
  Context (InitFollower : iProp Σ).
  Notation MTC := (client_handler_at_follower_user_params γL γM N f2csa).
  Context (HInitFollowerSpec :
          ⊢  (∀ (MTS : MTS_spec_params MTC) A,
                @run_server_spec _ _ _ _ _ InitFollower follower_si MTS A)).
  Context (γF : gname).

  Definition init_follower_res : iProp Σ :=
    Global_Inv γL γM N ∗
    own_log_auth γF (1/2) [] ∗
    own_logL_obs γL [] ∗
    InitFollower ∗
    known_replog_token f2csa γF.

  Definition init_follower_spec_internal A : iProp Σ :=
        ⌜DB_addrF ∈ A⌝ →
        ⌜f2csa ∈ A⌝ →
        ⌜f2lsa ∉ A⌝ →
        ⌜ip_of_address f2csa = ip_of_address f2lsa⌝ →
        ⌜port_of_address f2csa ≠ port_of_address f2lsa⌝ →
        {{{ fixed A ∗
            f2csa ⤇ follower_si ∗
            DB_addrF ⤇ leaderF_si ∗
            init_follower_res ∗
            f2csa ⤳ (∅, ∅) ∗
            f2lsa ⤳ (∅, ∅) ∗
            free_ports (ip_of_address f2csa) {[port_of_address f2csa]} ∗
            free_ports (ip_of_address f2lsa) {[port_of_address f2lsa]} }}}
          init_follower (s_serializer DB_serialization)
            #DB_addrF #f2lsa #f2csa @[ip_of_address f2csa]
        {{{ RET #(); True }}}.

  Lemma init_leader_spec_internal_holds A : ⊢ init_follower_spec_internal A.
  Proof.
    iIntros (HinA HinA2 HinFA HipEq HprNeq) "!# %Φ Hr HΦ".
    iDestruct "Hr" as
      "(#HA & #Hsi & #HsiF & HinitRes & Hmh & HmhF & Hfp & HfpF)".
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
      as "(#HGinv & HownF & #HobsL & Hinit & #HFtkn)".
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
    iExists logV, [].
    iSplit; first done.
    iFrame.
    iExists kvsV,  ∅.
    iSplit; first done.
    iSplit.
    { iPureIntro. apply valid_state_local_empty. }
    iFrame "#∗".
    iIntros (mγ mv) "#HLInv".
    wp_pures.
    symmetry in HipEq.
    rewrite {1} HipEq.
    admit. 
(*    wp_apply aneris_wp_fork.
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
         wp_apply (update_log_copy_loop_spec γL γM N _ γF mFγ
                    with "[HownF2]"); [ | done].
         iFrame "#∗".
         rewrite /leader_local_secondary_inv.
         rewrite /log_monitor_inv.
         by rewrite HipEq.
         Unshelve. done.
      -- rewrite /start_leader_processing_followers.
         iNext.
         wp_pures.
         assert (DB_addr ≠ DB_addrF) as Hneq.
         { intro Heq. destruct DB_addr, DB_addrF. by inversion Heq. }
         wp_apply
           (HInitLeaderFSpec $! (follower_handler_spec_params
                                   γL γM N mFγ γF mFv logLF Hneq) A _
             with "[$HsrvFinit $HmhF $HfpF]");  eauto with iFrame.
    - rewrite /start_leader_processing_clients.
      iNext.
      wp_pures.
      rewrite -HipEq.
      wp_apply
        (HInitLeaderSpec $! (client_handler_at_leader_spec_params
                               γL γM N mγ mv kvsL logL) A _
          with "[$HsrvInit $Hmh $Hfp]"); eauto with iFrame.
  Qed. *)
Admitted.

End Init_Follower_Proof.
