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
(** Instantiation of the client side specifications for making a new client
    socket and connect. *)
(* -------------------------------------------------------------------------- *)

From aneris.examples.reliable_communication.proof.client Require Import
     proof_of_make_client_skt
     proof_of_connect.

Section Client_API_spec_instantiation.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{!server_ghost_names}.
  Context `{!chanG Σ}.
  Context `{User_params: !Reliable_communication_service_params}.

  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Lemma make_client_skt_spec_holds clt_addr A:
    make_client_skt_spec
        User_params
        session_resources_instance
        clt_addr A.
  Proof.
    rewrite /make_client_skt_spec.
    rewrite /make_client_skt.
    rewrite /CltCanConnect /session_resources_instance.
    iIntros (Φ) "(H1 & H2 & H3 & H4) HΦ".
    iDestruct (make_client_skt_internal_spec_holds clt_addr $! Φ
                with "[$H1 $H2 $H3 $H4][HΦ]") as "Hspec".
    iNext. iIntros (skt h s) "Hr". iApply "HΦ". eauto with iFrame.
    iApply "Hspec".
  Qed.

  Lemma make_connect_skt_spec_holds skt clt_addr:
        connect_spec
            User_params
            session_resources_instance
            skt clt_addr.
  Proof.
    rewrite /make_client_skt_spec.
    rewrite /connect_spec.
    rewrite /CltCanConnect /session_resources_instance.
    iIntros (Φ) "(%h & %s & Hres) HΦ".
    iApply (connect_internal_spec with "[Hres][HΦ]").
    - iExists _, _. iFrame.
    - iNext. iIntros (γe c) "(Hpost & _)".
      iApply "HΦ". iExists _. iFrame.
  Qed.

End Client_API_spec_instantiation.
