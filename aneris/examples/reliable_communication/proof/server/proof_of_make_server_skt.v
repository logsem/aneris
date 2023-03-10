From iris.proofmode Require Import tactics.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants mono_nat.
From stdpp Require Import namespaces.
From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.aneris_lang.lib Require Import assert_proof.
From aneris.aneris_lang.lib Require Import pers_socket_proto lock_proof queue_proof.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.reliable_communication Require Import client_server_code user_params.
From aneris.examples.reliable_communication.resources Require Import
     chan_endpoints_resources socket_interp.
From aneris.examples.reliable_communication.proof.server Require Import server_resources.

Section Proof_of_make_server_skt.
  Context `{!anerisG Mdl Σ}.
  Context `{!chanG Σ}.
  Context `{!lockG Σ}.
  Context `{!Reliable_communication_service_params}.
  Context `{!server_ghost_names}.

  Notation srv_ip := (ip_of_address RCParams_srv_saddr).

  Lemma make_server_skt_internal_spec :
    {{{ unbound srv_ip {[port_of_address RCParams_srv_saddr]} ∗
        RCParams_srv_saddr ⤳ (∅, ∅) ∗
        RCParams_srv_saddr ⤇ server_interp ∗
        known_sessions ∅ ∗
        own γ_srv_known_messages_R_name (● ∅) ∗
        own γ_srv_known_messages_R_name (◯ ∅) ∗
        own γ_srv_known_messages_T_name (● ∅) ∗
        own γ_srv_known_messages_T_name (◯ ∅)
     }}}
       make_server_skt
       (s_serializer RCParams_srv_ser)
       (s_serializer RCParams_clt_ser)
       #RCParams_srv_saddr
       @[srv_ip]
     {{{ srv_skt, RET srv_skt; isServerSocketInternal srv_skt false }}}.
  Proof.
    iIntros (Φ) "(Hprts & Hmh & #Hsi & Hkn) HΦ".
    wp_lam. wp_lam.
    wp_socket h as "Hh". wp_pures.
    wp_socketbind.
    wp_alloc l as "Hl". iApply "HΦ". iExists l; iSplit; [done|].
    iLeft. iSplit; [done|]. iExists _, _, _. iFrame "#∗"; eauto.
  Qed.

End Proof_of_make_server_skt.
