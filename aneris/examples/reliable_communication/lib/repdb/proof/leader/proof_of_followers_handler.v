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
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code model.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params events.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import
     ras
     log_resources
     resources_def
     resources_global_inv
     resources_local_inv.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import
     repdb_serialization
     log_proof.
From aneris.examples.reliable_communication.lib.repdb.proof.leader
     Require Import
     followers_mt_user_params.

Import gen_heap_light.
Import lock_proof.
Import log_code.
(* -------------------------------------------------------------------------- *)
Section Followers_MT_spec_params.

  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (γL γM : gname).
  Context (mγ γF : gname) (mv : val) (logFLoc : loc).
  Context (HipNeq : DB_addr ≠ DB_addrF).
  Notation MTU_F := (follower_handler_user_params γL γM).


  Definition handler_cloj : val :=
    λ: "mon" "req", follower_request_handler #logFLoc "mon" "req".

  Lemma follower_request_handler_spec :
    ∀ reqv reqd,
    {{{ leader_local_secondary_inv γL logFLoc γF mγ mv ∗
        lock_proof.locked mγ ∗
        (log_monitor_inv_def
             (ip_of_address MTU_F.(MTS_saddr)) γF (1/4) logFLoc
             (leader_local_secondary_res γL γF)) ∗
        MTU_F.(MTS_handler_pre) reqv reqd }}}
      handler_cloj mv reqv @[ip_of_address MTU_F.(MTS_saddr)]
    {{{ repv repd, RET repv;
        ⌜Serializable rep_l2f_serialization repv⌝ ∗
        lock_proof.locked mγ ∗
        (log_monitor_inv_def
             (ip_of_address MTU_F.(MTS_saddr)) γF (1/4) logFLoc
             (leader_local_secondary_res γL γF)) ∗
        MTU_F.(MTS_handler_post) repv reqd repd }}}.
  Proof.
    iIntros (reqv reqd Φ) "(#Hmon & Hlocked & HR & Hpre) HΦ".
    rewrite /handler_cloj /follower_request_handler.
    simplify_eq /=.
    iDestruct "Hpre" as "(#HGinv & -> & #Hobs)".
    iDestruct "HR" as (logV logM) "(%Hlog & Hpl & HLog & #Htkn & #HobsL)".
    iDestruct "Hobs" as (γF') "(Htkn' & _ & Hobs)".
    iDestruct (known_replog_token_agree with "[$Htkn'][$Htkn]") as "->".
    iDestruct (own_obs_prefix with "[$HLog][$Hobs]") as "%Hprefix".
    apply prefix_length in Hprefix.
    wp_pures.
    wp_apply (wp_log_wait_until
               with "[$Hmon $Hlocked $Hpl $HLog $HobsL][HΦ]").
    { naive_solver. }
    iNext.
    iIntros (logV' logM').
    iIntros "(%Hlen' & %Hlog' & Hlocked & HmainRes & Hpl & HmainLog)".
    wp_pures.
    wp_apply (wp_log_get with "[$Hpl]"); first done.
    iIntros (we) "(%Hsome & _ & Hpl)".
    iDestruct (get_obs with "HmainLog") as "#Hobs'".
    apply nth_error_split in Hsome.
    destruct Hsome as (l1 & l2 & HeqlogM' & Hlen1).
    iDestruct (get_obs_prefix with "Hobs'") as "Hobsl1"; first done.
    iDestruct (obs_length_agree with "[$Hobsl1][$Hobs]") as "->"; first done.
    assert (logM' =  (reqd ++ [we]) ++ l2) as HeqlogM'2.
    { by list_simplifier. }
    clear HeqlogM'.
    iDestruct (get_obs_prefix with "Hobs'") as "HobsWe"; first done.
    iDestruct "HmainRes" as "(_  & #HobsL')".
    iDestruct (get_obs_prefix with "HobsL'") as "HobsLWe"; first done.
    iApply fupd_aneris_wp.
    iMod (Obs_we_serializable _ _ DB_addr with "[$HGinv][$HobsLWe]") as "%Hser";
    [done| by iLeft |].
    iModIntro.
    wp_apply network_util_proof.wp_unSOME; first done.
    iIntros "_".
    iApply ("HΦ" $! ($ we) (reqd ++ [we])).
    iSplit; first done.
    iFrame "Hlocked".
    iSplitL.
    { iExists logV', logM'. by iFrame "#∗". }
    iExists we.
    iSplit; first done.
    iExists γF. iFrame "#∗".
  Qed.

  Global Instance follower_handler_spec_params :  @MTS_spec_params _ _ _ _ MTU_F :=
    {|
      MTS_mR := (log_monitor_inv_def
                   (ip_of_address MTU_F.(MTS_saddr)) γF (1/4) logFLoc
                   (leader_local_secondary_res γL γF));
      MTS_mγ := mγ;
      MTS_mv := mv;
      MTS_handler := handler_cloj;
      MTS_handler_spec := follower_request_handler_spec;
    |}.

End Followers_MT_spec_params.
