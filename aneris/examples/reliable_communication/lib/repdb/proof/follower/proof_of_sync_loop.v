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
  Context (γL γM : gname) (N : gmap socket_address gname) (sa : socket_address) (kvsL logL : loc).

  Global Instance MTU : MTS_user_params.
  Proof. apply (follower_handler_user_params γL γM N). Defined.

 Definition own_replog_loop l : iProp Σ :=
    ∃ γF, known_replog_token sa γF ∗ own_replog_obs γL DB_addrF l ∗
    own_log_auth γF (1/4) l.

  Lemma sync_loop_spec
        (mγ : gname) (mv : val) (reqh : val) (logM : wrlog) (n : nat) :
    n = length logM →
    {{{ Global_Inv γL γM N ∗
        (follower_local_inv γL kvsL logL sa mγ mv) ∗
        make_request_spec reqh sa ∗
        own_replog_loop logM
    }}}
      sync_loop #kvsL #logL mv reqh #n @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Hn Φ) "((#HnMap & #HGinv) & (%γF' & #HinvL) & #Hreqh & HlogM) HΦ".
    rewrite /sync_loop.
    do 12 wp_pure _.
    iLöb as "IH" forall (n logM Hn).
    iDestruct "HlogM" as (γF) "(#Hknw & #HobsL & HlogM)".
    iDestruct (get_obs with "[$HlogM]") as "#HobsF".
    wp_pures.
    rewrite /make_request_spec.
    wp_apply ("Hreqh" $! _ logM).
    { iSplit; first by iPureIntro; apply _. iFrame "#"; naive_solver. }
    iIntros (logM' repv) "Hpost".
    iDestruct "Hpost" as (we) "(-> & %Hwekey & %HweSer & %Hlen & -> & #HobsLF')".
    do 13 wp_pure _.
    rewrite Hlen Hn.
    wp_apply wp_assert.
    wp_pures.
    iSplit.
    { iPureIntro.
      by case_bool_decide. }
    iNext.
    wp_pures.
    wp_apply (monitor_acquire_spec with "[HinvL]"); first by iFrame "#".
    iIntros (v) "( -> & Hlocked & Hres)".
    iDestruct "Hres" as (logV logM') "(%Hlog & Hpl & HLog & HRes)".
   iDestruct "HRes" as (kvsV kvsM) "(%Hkvs & %HvalidLocal & Hpm & #Hknw' & #HobsL')".
    iAssert (⌜γF' = γF⌝)%I as "->".
    { iApply (known_replog_token_agree with "[$Hknw'][$Hknw]"). }
    wp_pures.
    iDestruct (own_log_auth_combine with "HLog HlogM") as "(HlMhalf & ->)".
    set (a := {|we_key := (we_key we); we_val := (we_val we);
                               we_time := (length logM : int_time.(Time))|}).
    simplify_eq /=.
    wp_apply (wp_log_add_entry _ _ _ logM a with "[$Hpl]"); [done|].
    iIntros (logV') "(%Hlog' & Hpl')".
    wp_pures.
    wp_load.
    wp_apply (wp_map_insert $! Hkvs).
    iIntros (m' Hm').
    wp_bind (Store _ _).
    wp_store.
    wp_pures.
    iApply fupd_aneris_wp.
    iInv DB_InvName
        as (lMG kvsMG) ">(%HkG & %Hdom & %Hdisj & HmS & HlM & HknwF & HmapF & %HvalidG)".
    iDestruct (known_replog_in_N with "[$HknwF $Hknw]") as %HNsa.
    iDestruct (big_sepM_lookup_acc _ _ sa γF HNsa with "[$HmapF]")
      as "((%lF & (_ & #HobsL'' & HlMhalf')) & Hcl)".
    iDestruct (own_log_auth_combine with  "HlMhalf HlMhalf'") as "(HlFull & ->)".
    rewrite Qp_quarter_quarter Qp_half_half.
    iAssert (own_replog_obs γL DB_addrF (lF ++ [we])) as "HobsLF'cpy".
    { by done. }
    iDestruct "HobsLF'" as (γF') "(_ & HobsLwe & HobsLFwe)".
    iMod (own_log_auth_update _ _ (lF ++ [we]) with "[$HlFull]") as "HlFull".
    { by apply prefix_app_r. }
    rewrite - {4} Qp_half_half.
    iDestruct (own_log_auth_split with "HlFull") as "(HlogM & HlogL)".
    iDestruct (get_obs with "[$HlogL]") as "#Hobsfr2".
    iModIntro.
    rewrite /global_inv_def.
    iSplitL "HlM HlogM HmS Hcl HknwF".
    { iAssert (⌜lF ++ [we] `prefix_of` lMG⌝)%I as "%Hprefix".
      { iApply (own_obs_prefix with "[$HlM][$HobsLwe]"). }
      iNext. iExists _, _. iFrame.
      do 3 (iSplit; first done).
      iSplit; last done.
      iApply ("Hcl" with "").
      iExists (lF ++ [we]).
      iFrame "#∗". }
    iModIntro.
    rewrite - Qp_quarter_quarter.
    iDestruct (own_log_auth_split with "HlogL") as "(HlogL1 & HlogL2)".
    wp_apply (monitor_release_spec
               with "[$HinvL $Hlocked Hpl' Hpm HlogL1]").
    { iExists _, _. iFrame.
      iSplitR.
      eauto with iFrame.
      - iPureIntro.
        by assert (a = we) as -> by by destruct we; naive_solver.
      - iExists m', (<[we_key we:=we_val we]> kvsM).
        iFrame.
        iSplit; first done.
        iSplit; last by iFrame "#∗".
        iPureIntro.
        by apply (valid_state_local_update lF kvsM (we_key we) we). }
    iIntros (v ->).
    do 3 wp_pure _.
    replace (#(length lF + 1)) with (#(length lF + 1)%nat); last first.
    { do 2 f_equal.
      lia. }
    iApply ("IH" $! (length lF + 1)%nat (lF ++ [we]) with "[][HlogL2][$HΦ]").
    { rewrite last_length.
      iPureIntro; lia. }
    iFrame "#∗"; eauto.
  Qed.

End SyncLogCopy_Proof.
