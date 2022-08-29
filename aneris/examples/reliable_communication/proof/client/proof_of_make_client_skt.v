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
From aneris.examples.reliable_communication.proof.client Require Import client_resources.

Section Proof_of_make_client_skt.
  Context `{!anerisG Mdl Σ}.
  Context `{!chanG Σ}.
  Context `{!lockG Σ}.
  Context `{!Reliable_communication_service_params}.
  Context `{!server_ghost_names}.

  Definition make_client_skt_internal_spec
    (clt_addr : socket_address) : iProp Σ :=
    {{{ free_ports (ip_of_address clt_addr) {[port_of_address clt_addr]} ∗
        clt_addr ⤳ (∅, ∅) ∗
        RCParams_srv_saddr ⤇ server_interp ∗
        unallocated {[clt_addr]}
     }}}
       make_client_skt
       (s_serializer RCParams_clt_ser)
       (s_serializer RCParams_srv_ser)
       #clt_addr
       @[ip_of_address clt_addr]
     {{{ skt h s, RET skt;
         isClientSocketInternal skt h s clt_addr true ∅ ∅ }}}.

  Lemma make_client_skt_internal_spec_holds clt_addr
    : ⊢ make_client_skt_internal_spec clt_addr.
  Proof.
    rewrite /make_client_skt_internal_spec /make_client_skt.
    iIntros (Φ) "!# (Hprts & Hmh & #Hsrvi & Hf) HΦ".
    wp_pures. wp_lam. wp_socket h as "Hh". wp_pures.
    iApply (aneris_wp_socket_interp_alloc_singleton client_interp with "Hf").
    iIntros "Hf".
    wp_socketbind.
    wp_pures.
    iApply "HΦ". iFrame "#∗"; eauto.
  Qed.

End Proof_of_make_client_skt.
