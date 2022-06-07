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
    λ: "mv" "reqv", client_request_handler_at_leader #kvsL #logL "mv" "reqv".

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
  Admitted.
   (* iIntros (Φ) "(#Hmon & Hkey & HR & Hpre) HΦ".
    rewrite /client_request_handler_at_leader.
    wp_pures.
    rewrite /ReqPre.
    iDestruct "Hpre" as "(#HGinv & [HpreW | HpreR])".
    - admit.
    - iDestruct "HpreR" as (k we q Hkeys Hreqd ->) "Hk".
      wp_pures.
      rewrite{2} /leader_local_main_inv_def.
      iDestruct "HR" as (lV mV mM lM Hmap Hlog HvalidL) "(Hm & Hl & HlogL)".
      wp_load.
      wp_apply (wp_map_lookup $! Hmap).
      iIntros (v Hv).
      wp_pures.
      destruct (mM !! k) eqn:Hmk; rewrite Hmk in Hv.
      + admit.
      + iApply ("HΦ" $! _ (inr None)).
        iSplit.
        * rewrite Hv. rewrite /rep_l2c_serialization.
          iPureIntro.
          rewrite /Serializable /= /sum_valid_val /=; eauto.
          exists (InjLV #()). right. split; first done. by right.
        * iFrame "Hkey".
          iSplitR "Hk".
          ** admit.
          ** iRight. iIntros (k0 wo0 q0 Hreqd0).
             iExists v.
             iSplit.
             admit.
             iSplit; first done.
             rewrite Hreqd0 in Hreqd. inversion Hreqd. subst.
             iFrame. iLeft. admit.

          rewrite /option_valid_val.
          exists (InjLV #()).
          Eapply option_is_ser_valid. rewrite option_valid_val. /=; eauto..
          eauto. done. apply (sum_is_ser_valid _ _ _ ""). simplify_eq.
          simpl. iPureIntro. simplify_eq /=.
          eapply sum_is_ser_valid. rewrite /sum_is_ser. simplify_eq /=.
          eexists _, _. right. split; eauto. done.
       + admit.
      + iFrame "Hkey". *)


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
