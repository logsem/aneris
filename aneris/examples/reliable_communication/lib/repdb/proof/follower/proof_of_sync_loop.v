From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof assert_proof.
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
     Require Import db_params time events resources.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import
     ras log_resources resources_def
     resources_global_inv resources_local_inv.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import
     repdb_serialization log_proof.
From aneris.examples.reliable_communication.lib.repdb.proof.leader
     Require Import
     followers_mt_user_params.

Import log_proof.

Section SyncLogCopy_Proof.
  Context `{!anerisG Mdl Σ, dbparams : !DB_params, !IDBG Σ}.
  Context (γL γM γF : gname) ( sa : socket_address) (kvsL logL : loc).

  Global Instance MTU : MTS_user_params.
  Proof. apply (follower_handler_user_params γL γM). Defined.

 Definition own_replog_loop l : iProp Σ :=
    known_replog_token sa γF ∗ own_replog_obs γL DB_addrF l ∗
    own_log_auth γF (1/4) l.

  Lemma sync_loop_spec
        (mγ : gname) (mv : val) (reqh : val) (logM : wrlog) (n : nat) :
    n = length logM →
    {{{ Global_Inv γL γM ∗
        follower_local_inv γL kvsL logL sa γF mγ mv ∗
        make_request_spec reqh sa ∗
        own_replog_loop logM
    }}}
      sync_loop #kvsL #logL mv reqh #n @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Hn Φ) "(#HGinv & #HinvL & #Hreqh & HlogM) HΦ".
    rewrite /sync_loop. do 12 wp_pure _.
    iLöb as "IH" forall (n logM Hn).
    iDestruct "HlogM" as "(#Hknw & #HobsL & HlogM)".
    iDestruct (get_obs with "[$HlogM]") as "#HobsF".
    wp_pures. rewrite /make_request_spec. wp_apply ("Hreqh" $! _ logM).
    { iSplit; first by iPureIntro; apply _. iFrame "#"; naive_solver. }
    iIntros (logM' repv) "Hpost".
    iDestruct "Hpost" as (we) "(-> & %Hlen & -> & #HobsLF')".
    do 13 wp_pure _.
    rewrite Hlen Hn.
    wp_apply wp_assert.
    wp_pures. iSplit.
    { iPureIntro. by case_bool_decide. }
    iNext. wp_pures.
    wp_apply (monitor_acquire_spec with "[HinvL]"); first by iFrame "#".
    iIntros (v) "( -> & Hlocked & Hres)".
    wp_pures.
   (*iDestruct "Hres" as (logV logM) "(%Hlog & Hpl & HmainLog & HmainRes)".
    iAssert (⌜lF `prefix_of` logM⌝)%I as "%Hprefix".
    { iDestruct "Hloop" as "(_ & Hobs & _)".
      iApply (own_obs_prefix with "[$HmainLog][$Hobs]"). }
    assert (length lF ≤ length logM) as Hlen2.
    { by apply prefix_length. }
    wp_apply (wp_log_wait_until
               with "[$HinvL $Hlocked $Hpl $HmainLog $HmainRes][Hloop HΦ]").
    { naive_solver. }
    iNext.
    iIntros (logV' logM').
    iIntros "(%Hlen' & %Hlog' & Hlocked & HmainRes & Hpl & HmainLog)".
    wp_pures.
    wp_load.
    wp_pures.
    iAssert (⌜lF `prefix_of` logM'⌝)%I as "%Hprefix2".
    {  iDestruct "Hloop" as "(_ & Hobs & _)".
       by iDestruct (own_obs_prefix with "[$HmainLog][$Hobs]") as "%Hprefix2". }
    iDestruct (get_obs with "[$HmainLog]") as "#HobsM'".
    wp_apply (monitor_release_spec
               with "[$HinvL $Hlocked Hpl HmainLog HmainRes]").
    iExists _, _. eauto with iFrame.
    iIntros (v ->).
    wp_pures.
    rewrite HipEq.
    wp_apply (monitor_acquire_spec with "[$HinvF]").
    iIntros (v) "( -> & Hlocked & Hres)".
    wp_pures.
    iDestruct "Hres" as (logVF logMF) "(%HlogF & HplF & HLogOwnF & HResF)".
    wp_store.
    iDestruct "Hloop" as "(#HknownTkn & #Hobs & HownLoop)".
    iDestruct (own_log_auth_combine
                with "[$HLogOwnF][$HownLoop]") as "(HownFHalf1 & ->)".
    assert (length lF < length logM') by lia.
    clear logM Hlog Hprefix logV n Hlen Hlen' Hlen2.
    rewrite /Global_Inv /global_inv_def.
    iApply fupd_aneris_wp.
    iInv DB_InvName as ">HGinvRes" "Hcl".
    iDestruct "HGinvRes" as (L M N Hkes) "HGinvRes".
    iDestruct "HGinvRes" as "(HownS & HownL & HknownN & HmapN & %HvSt)".
    iAssert (⌜N !! DB_addrF = Some γF⌝)%I as "%HinF".
    by iDestruct (known_replog_in_N with "[$HknownN $HknownTkn]") as "%HinN".
    iDestruct (big_sepM_lookup_acc _ N DB_addrF γF with "[$HmapN]")
      as "(Hres & HmapN)"; [done|].
    iDestruct "Hres" as (l) "(#HknownTkn' & #Hobs' & HownFHalf2)".
    iDestruct (own_log_auth_combine
                with "[$HownFHalf1][$HownFHalf2]") as "(HownF & ->)".
    rewrite Qp_quarter_quarter Qp_half_half.
    iMod (own_log_auth_update _ l logM'
           with "[$HownF]") as "HownF"; first done.
    rewrite -Qp_half_half.
    rewrite {1} Qp_half_half.
    iDestruct (own_log_auth_split with "HownF") as "[HownF1 HownF2]".
    rewrite -Qp_quarter_quarter.
    rewrite {1} Qp_quarter_quarter.
    iMod ("Hcl" with "[HownF1 HmapN HknownN HownS HownL]") as "_".
    { iNext. iExists L, M, N. iFrame "#∗".
      iSplit; first done.
      iSplit; last done.
      iApply "HmapN".
      iExists logM'. iFrame "#∗". }
    iModIntro.
    iDestruct (own_log_auth_split with "HownF2") as "[HownF1 HownF2]".
    wp_apply (monitor_broadcast_spec
               with "[$HinvF $Hlocked HplF HResF HownF1]").
    { iExists _, logM'.
      rewrite /leader_local_secondary_res.
      iFrame "#∗".
      done. }
    iIntros "(Hlocked & Hres)".
    wp_pures.
    wp_apply (monitor_release_spec with "[$HinvF $Hlocked $Hres]").
    iIntros (v ->).
    do 4 wp_pure _.
    assert (∃ lV : val, logV' = (lV, #(length logM'))%V ∧ is_list logM' lV)
           as (lV & -> & Hlst') by done.
    do 1 wp_pure _.
    iApply ("IH" $! logM' with "[//][$HΦ][$HownF2]").
    iFrame "#∗".
  Qed. *)
  Admitted.

End SyncLogCopy_Proof.
