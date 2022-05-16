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

From aneris.examples.reliable_communication.proof.common_user Require Import
     proof_of_send
     proof_of_recv.

Section Send_Recv_API_spec_instantiation.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{!chanG Σ}.
  Context `{!server_ghost_names}.
  Context `{User_params: !Reliable_communication_service_params}.

  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Lemma send_spec_holds (c : val) v p ip serA:
    send_spec (c : val) v p ip serA.
  Proof.
    rewrite /send_spec.
    iIntros (Φ) "(H1 & H2) HΦ".
    iDestruct "H1" as (γe) "H1".
    iApply (send_spec_internal _ _ _ p with "[$][HΦ]").
    iNext. iIntros "Hc". iApply "HΦ".
    iExists _. iFrame.
  Qed.

  Lemma send_tele_spec_holds
         TT c (tt : TT) (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) ip serA:
    send_spec_tele
         TT c (tt : TT)
      (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) ip serA.
  Proof.
    rewrite /send_spec_tele.
    iIntros (Φ) "(H1 & Hp & H2) HΦ".
    iDestruct "H1" as (γe) "H1".
    iApply (send_spec_tele_internal _ _ _ _ _ _ with "[-HΦ][HΦ]").
    - by iFrame.
    - iNext. iIntros "Hc". iApply "HΦ".
    iExists _. iFrame.
  Qed.

  Lemma try_recv_spec_holds
        TT (c : val) (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) ip ser:
    try_recv_spec
        TT (c : val) (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) ip ser.
  Proof.
    rewrite /try_recv_spec.
    iIntros (Φ) "H1 HΦ".
    iDestruct "H1" as (γe) "H1".
    iApply (try_recv_spec_internal _ _ _  with "[$][HΦ]").
    iNext. iIntros (w) "Hc". iApply "HΦ".
    iDestruct "Hc" as "[(-> & Hc)|(%tt & -> & Hc & Hp)]".
    - iLeft. iSplit; first done.
      iExists _. iFrame.
    - iRight.
      iExists _.
      iSplit; first done.
      iFrame.
      iExists _. iFrame.
  Qed.

  Lemma recv_spec_holds
        TT (c : val) (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) ip ser:
    recv_spec
        TT (c : val) (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) ip ser.
  Proof.
    rewrite /recv_spec.
    iIntros (Φ) "H1 HΦ".
    iDestruct "H1" as (γe) "H1".
    iApply (recv_spec_internal _ _ _  with "[$][HΦ]").
    iNext. iIntros (w) "(Hc & Hp)". iApply "HΦ". iFrame.
    iExists _. iFrame.
  Qed.


End Send_Recv_API_spec_instantiation.
