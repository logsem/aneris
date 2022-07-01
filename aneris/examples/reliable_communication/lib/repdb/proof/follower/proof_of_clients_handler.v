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
From aneris.examples.reliable_communication.lib.repdb.proof.follower
     Require Import clients_at_follower_mt_user_params.

Import gen_heap_light.
Import lock_proof.

Section Clients_MT_spec_params.

  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (γL γM : gname) (N : gmap socket_address gname) (sa : socket_address).
  Context (mγ : gname) (mv : val) (kvsL logL : loc).

  (* Definition handler_cloj : val := *)
  (*   λ: "mon" "req", client_request_handler_at_follower #kvsL "mon" "req". *)
  (* Definition handler_cloj' mon : val := *)
  (*   λ: "req", handler_cloj mon "req". *)

  Notation MTU := (client_handler_at_follower_user_params γL γM N sa).

  Lemma client_request_handler_at_follower_spec γF :
    ∀ reqv reqd,
    {{{ is_monitor
           MTU.(MTS_mN)
            (ip_of_address MTU.(MTS_saddr)) mγ mv
            (known_replog_token sa γF ∗
               log_monitor_inv_def
                 (ip_of_address MTU.(MTS_saddr))
                 γF ¼ logL (follower_local_res γL kvsL sa γF)) ∗
          MTU.(MTS_handler_pre) reqv reqd }}}
      client_request_handler_at_follower #kvsL mv reqv @[ip_of_address MTU.(MTS_saddr)]
    {{{ repv repd, RET repv;
        ⌜Serializable (rep_f2c_serialization) repv⌝ ∗
        MTU.(MTS_handler_post) repv reqd repd }}}.
  Proof.
    iIntros (reqv reqd Φ) "(#Hmon & Hpre) HΦ".
    rewrite /client_request_handler_at_follower.
    wp_pures.
    wp_apply (monitor_acquire_spec with "[Hmon]"); first by iFrame "#".
    iIntros (v) "(-> & HKey & #Hknw & HR)".
    iDestruct "HR" as (lV lM) "(%Hlog & Hpl & HlogL & HR)".
    iDestruct "HR" as (kvsV kvsM) "(%Hkvs & %HvalidLocal & Hpm & _ & #Hobs)".
    iDestruct "Hpre" as "(#HGinv & HpreR)".
    iDestruct "HpreR" as (k h Hkeys Hreqd ->) "(%γF' & #(Hknown & HobsL & Hobs2))".
    wp_pures.
    wp_load.
    iDestruct (known_replog_token_agree with "[$Hknown][$Hknw]") as "->".
    iDestruct (own_obs_prefix _ _ _ h with "[$HlogL][$Hobs2]") as "%Hprefixh".
    iDestruct (get_obs with "[$HlogL]") as "#HobsF".
    inversion HvalidLocal.
    wp_apply fupd_aneris_wp.
    iAssert (|={⊤}=>
               (⌜kvsM !! k = None⌝ ∗ ⌜at_key k lM = None⌝) ∨
                 (∃ a : write_event, ⌜kvsM !! k = Some (we_val a)⌝ ∗
                     ⌜at_key k lM = Some a⌝))%I
      as ">Hpost".
    { destruct (kvsM !! k) as [v|] eqn:Hmk.
      - iModIntro. iRight.
        apply DB_LSTV_in_mem_log_some_coh_local in Hmk.
        destruct Hmk as (we0 & Hwe0L & <-).
        iExists _.
        iSplit; first done.
        by iPureIntro.
      - iModIntro.
        iLeft.
        iSplit; first done.
        iPureIntro.
        by apply DB_LSTV_in_mem_log_none_coh_local in Hmk. }
    iModIntro.
    wp_apply (wp_map_lookup $! Hkvs).
    iIntros (v Hkm).
    destruct (kvsM !! k) eqn:Hmk.
    - iDestruct "Hpost" as "[(%Habs & _)|Hpost]"; first done.
      iDestruct "Hpost" as (a Ha) "%Hwe".
      assert (v = SOMEV (we_val a)) as ->.
      { rewrite Hmk in Hkm.
        naive_solver. }
      wp_pures.
      wp_apply (monitor_release_spec with "[$Hmon Hpm Hpl HlogL $HKey]").
      { iSplitR. iFrame "Hknw".
        iExists _, _.  iSplit; first done.
        iFrame "#∗". iExists _, _. by iFrame. }
      iIntros (v ->).
      do 2 wp_pure _.
      iApply ("HΦ" $! (SOMEV (we_val a)) lM).
      iSplit.
      { iPureIntro.  assert (k ∈ dom kvsM) as Hk by by apply elem_of_dom.
         assert (v0 = (we_val a)) as Heqa by naive_solver.
         rewrite Heqa in Hmk.
         rewrite Hmk in Hkm.
         specialize (DB_LSTV_mem_serializable_vs_local k (we_val a) Hmk).
         apply _. }
      simpl. rewrite /log_monitor_inv_def /ReqPost.
      iExists k, h, lM.
      do 3 (iSplit; first done).
      iFrame "#".
      iSplit.
      { iFrame "#"; eauto. }
      iRight.
      iExists a.
      eauto.
    - wp_pures.
      wp_apply (monitor_release_spec with "[$Hmon Hpm Hpl HlogL $HKey]").
      { iSplitR. iFrame "Hknw".
        iExists _, _.  iSplit; first done.
        iFrame "#∗". iExists _, _. by iFrame. }
      iIntros (v' ->).
      do 2 wp_pure _.
      iApply ("HΦ" $! _ lM).
      iDestruct "Hpost" as "[(_ & %Hnone) |%Habs]"; [|naive_solver].
      assert (v = NONEV) as ->.
      { rewrite Hmk in Hkm.
        naive_solver. }
      iSplit.
      { rewrite /rep_f2c_serialization.
        iPureIntro.
        apply _. }
      simpl.
      rewrite /log_monitor_inv_def /ReqPost.
      iExists k, h, lM.
      do 3 (iSplit; first done).
      iFrame "#∗".
      iSplit.
      { iFrame "#"; eauto. }
      iLeft.
      done.
  Qed.

End Clients_MT_spec_params.
