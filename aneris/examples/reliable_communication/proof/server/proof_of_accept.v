From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants mono_nat.
From stdpp Require Import namespaces.
From aneris.aneris_lang Require Import ast tactics.
From iris.algebra.lib Require Import excl_auth.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_proof.
From aneris.aneris_lang.lib Require Import assert_proof.
From aneris.aneris_lang.lib Require Import pers_socket_proto lock_proof queue_proof.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From actris.channel Require Export proto.
From stdpp Require Import base tactics telescopes.
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.resources Require Import
     chan_endpoints_resources
     socket_interp.
From aneris.examples.reliable_communication.proof.common_protocol Require Import
     proof_of_send_from_chan_loop.
From aneris.examples.reliable_communication.proof.server Require Import
     server_resources.


Section Proof_of_accept.
  Context `{!anerisG Mdl Σ, !Reliable_communication_service_params, !chanG Σ, !lockG Σ}.
  Context `{!server_ghost_names}.

  Context (N : namespace).

  Lemma accept_internal_spec (skt : val)  :
    {{{ isServerSocketInternal skt true }}}
      accept skt @[ip_of_address RCParams_srv_saddr]
    {{{ c (clt_addr: socket_address), RET (c, #clt_addr);
        (isServerSocketInternal skt true) ∗
        c ↣{ ip_of_address RCParams_srv_saddr, RCParams_srv_ser} iProto_dual RCParams_protocol }}}.
  Proof.
    iIntros (Φ) "HisServer HΦ".
    wp_lam.
    iDestruct "HisServer" as (srv_skt_l <-) "[( %Habs & _)|(_ & Hres)]"; [done|].
    iDestruct "Hres" as (γ_qlk qlk chan_queue_l) "(Hl & #Hqlk)".
    wp_load. do 8 wp_pure _. wp_lam.  wp_pure _. wp_let.
    iLöb as "IH" forall (chan_queue_l) "Hqlk".
    wp_pures.
    wp_apply (acquire_spec with "[$Hqlk] [Hl HΦ]").
    iNext. iIntros (v) "(-> & Hlocked & HlkRes)".
    wp_pures.
    iDestruct "HlkRes" as (chan_queue_v chan_queue_vs) "(Hcql & %Hq & HresS)".
    wp_load.
    wp_apply (wp_queue_is_empty $! Hq).
    iIntros (b Hb).
    destruct b; wp_pures.
    - wp_apply (release_spec with "[$Hlocked $Hqlk Hcql HresS]").
      + iExists _, _; eauto with iFrame.
      + iIntros (v ->). do 4 wp_pure _. by iApply ("IH" with "[$Hl] [$HΦ]").
    - wp_load.
      wp_apply (wp_queue_take_opt $! Hq).
      iIntros (rv [(Habs & _)|(h & t & tv & Hvs & Hrv & Hcnd)]); [done|].
      wp_apply (wp_unSOME $! Hrv).
      iIntros (_); simpl.
      wp_pures.
      rewrite Hvs.
      iDestruct (big_sepL_cons _ h t with "HresS") as "(Hh & HresS)".
      iDestruct "Hh" as (c sa ->) "Hh".
      wp_pures. wp_store. wp_pures.
      wp_apply (release_spec with "[$Hlocked $Hqlk Hcql HresS]").
      + iExists _, _; eauto with iFrame.
      + iIntros (v ->). wp_pures. iApply "HΦ". iFrame.
        iExists srv_skt_l. iSplit; first done.
        iRight. iSplit; first done. eauto with iFrame.
  Qed.

End Proof_of_accept.
