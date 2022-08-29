From iris.algebra Require Import excl.
From iris.algebra.lib Require Import excl_auth.
From trillium.prelude Require Import finitary.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import coq_tactics reduction spec_patterns tactics.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import inject lock_proof list_proof pers_socket_proto.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.spec Require Import resources api_spec.
From aneris.examples.reliable_communication.resources Require Import prelude.
From aneris.examples.reliable_communication.instantiation
     Require Import instantiation_of_resources.

Set Default Proof Using "Type".

(* -------------------------------------------------------------------------- *)
(** Instantiation of the server side specifications socket and connect. *)
(* -------------------------------------------------------------------------- *)

From aneris.examples.reliable_communication.proof.server Require Import
     proof_of_make_server_skt
     proof_of_server_listen
     proof_of_accept.

Section Server_API_spec_instantiation.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{!chanG Σ}.
  Context `{!server_ghost_names}.
  Context `{User_params: !Reliable_communication_service_params}.

  Lemma make_server_skt_spec_holds :
    make_server_skt_spec
      User_params
      session_resources_instance.
  Proof.
    rewrite /make_server_skt_spec.
    rewrite /SrvInit /session_resources_instance /SrvInitRes /SrvCanListen.
    iIntros (Φ) "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) HΦ".
    iApply (make_server_skt_internal_spec with "[$][$HΦ]").
  Qed.

  Lemma server_listen_spec_holds :
    server_listen_spec
      User_params
      session_resources_instance.
  Proof.
    rewrite /server_listen_spec.
    rewrite /SrvCanListen /SrvListens.
    iIntros (skt Φ) "Hyp HΦ".
    simpl.
    iApply (server_listen_internal_spec with "[$][$HΦ]").
  Qed.

  Lemma accept_spec_holds :
    accept_spec
      User_params
      session_resources_instance.
  Proof.
    rewrite /server_listen_spec.
    rewrite /session_resources_instance !/SrvListens.
    rewrite /chan_mapsto_resource_instance.
    iIntros (skt Φ) "Hyp HΦ".
    iApply (accept_internal_spec with "[$Hyp][HΦ]").
    iNext.
    iIntros (γe c clt_addr) "(H1 & H2 & _)".
    iApply "HΦ".
    rewrite /SrvListens.
    iFrame.
    iExists _; iFrame.
  Qed.

End Server_API_spec_instantiation.
