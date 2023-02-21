From iris.algebra Require Import excl.
From iris.algebra.lib Require Import excl_auth.
From trillium.prelude Require Import finitary.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import coq_tactics reduction spec_patterns tactics.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import inject lock_proof list_proof pers_socket_proto.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.examples.reliable_communication Require Import  client_server_code.
From aneris.examples.reliable_communication.spec Require Import api_spec.
Set Default Proof Using "Type".
From aneris.examples.reliable_communication.spec Require Import prelude ras.
From aneris.examples.reliable_communication.resources Require Import prelude.

Section RA_instantiation.
  Context `{!anerisG Mdl Σ}.
  Context `{!SpecChanG Σ}.

  Global Instance chanG_instance_0 : chanG Σ :=
    Build_chanG
      Σ
      SpecChanG_session_escrow
      SpecChanG_ids
      SpecChanG_cookie
      SpecChanG_session_names_map
      SpecChanG_address
      SpecChanG_side
      SpecChanG_idxs
      SpecChanG_mhst
      SpecChanG_status.

End RA_instantiation.

Arguments chanG_instance_0 {_ _}.

(* -------------------------------------------------------------------------- *)
(** Instantiation of the dependent separation protocol `c ↣{ip, ser} p` using
    chan_endpoints_resources definitions. *)
(* -------------------------------------------------------------------------- *)


From aneris.examples.reliable_communication.resources Require Import
     chan_endpoints_resources.
From aneris.examples.reliable_communication.spec Require Import
     resources.

Section Chan_mapsto_intantiation.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  (* This is what currently prevents from having chan_mapsto_class one for all servers.
     Needs an additional layer of indirection of abstraction. *)
  Context `{!server_ghost_names}.
  Context `{!chanG Σ}.

  Definition chan_mapsto_instance_def (c : val) (p : iProto Σ) ip ser : iProp Σ :=
    ∃ γe, c ↣{γe, ip, ser} p.

  Lemma chan_mapsto_instance_def_contractive :
     ∀ (c : val) (ip : ip_address) (ser : serialization)
                                (n : nat),
                                Proper (dist_later n ==> dist n)
                                  (λ p : iProto Σ, chan_mapsto_instance_def c p ip ser).
  Proof.
    rewrite /chan_mapsto_instance_def iProto_mapsto_eq /iProto_mapsto_def; solve_contractive.
  Qed.

  Lemma chan_mapsto_instance_def_ne :
    ∀ (c : val) (ip : ip_address)
                                 (ser : serialization) (n : nat),
                                 Proper (dist n ==> dist n)
                                   (λ p : iProto Σ, chan_mapsto_instance_def c p ip ser).
  Proof.
    rewrite /chan_mapsto_instance_def iProto_mapsto_eq /iProto_mapsto_def; solve_proper.
  Qed.

  Lemma chan_mapsto_instance_def_proper :
    ∀ (c : val) (ip : ip_address)
                                 (ser : serialization),
                                 Proper (equiv ==> equiv)
                                   (λ p : iProto Σ, chan_mapsto_instance_def c p ip ser).
  Proof.
    rewrite /chan_mapsto_instance_def iProto_mapsto_eq /iProto_mapsto_def; solve_proper.
  Qed.

  Lemma chan_mapsto_instance_def_le :
    ∀ (c : val) (ip : ip_address) (ser : serialization) (p1 p2 : iProto Σ),
    chan_mapsto_instance_def c p1 ip ser  -∗ ▷ (p1 ⊑ p2) -∗ chan_mapsto_instance_def c p2 ip ser.
  Proof.
    iIntros (c ip ser p1 p2).
    iDestruct 1 as (γe1) "Hc1".
    iIntros "Hle".
    iExists γe1.
    iDestruct (iProto_mapsto_le γe1 c ip ser p1 p2 with "[Hc1][$Hle]" ) as "Hle";
      by rewrite iProto_mapsto_eq.
  Qed.

  Global Instance chan_mapsto_resource_instance : @Chan_mapsto_resource Σ :=
    {| chan_mapsto c p ip ser := chan_mapsto_instance_def c p ip ser;
      chan_mapsto_contractive := chan_mapsto_instance_def_contractive;
      chan_mapsto_nonExpansive := chan_mapsto_instance_def_ne;
      chan_mapsto_proper := chan_mapsto_instance_def_proper;
      chan_mapsto_le := chan_mapsto_instance_def_le;
    |}.


End Chan_mapsto_intantiation.

Arguments chan_mapsto_resource_instance {_ _ _ _ _ _}.

(* -------------------------------------------------------------------------- *)
(** Instantiation of the Session Resources using client and server concrete
    resources definition. *)
(* -------------------------------------------------------------------------- *)
From aneris.examples.reliable_communication Require Import user_params.
From aneris.examples.reliable_communication.proof.client Require Import client_resources.
From aneris.examples.reliable_communication.proof.server Require Import server_resources.

Section Session_Resources_intantiation.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{!chanG Σ}.
  Context `{!server_ghost_names}.
  Context `{UP: !Reliable_communication_service_params}.


   Definition SrvInitRes : iProp Σ :=
        known_sessions ∅ ∗
        own γ_srv_known_messages_R_name (● ∅) ∗
        own γ_srv_known_messages_R_name (◯ ∅) ∗
        own γ_srv_known_messages_T_name (● ∅) ∗
        own γ_srv_known_messages_T_name (◯ ∅).

   Arguments isClientSocketInternal { _ _ _ _ }.

   Global Instance session_resources_instance : SessionResources UP :=
     {| SrvInit := SrvInitRes;
        CltCanConnect skt clt_addr :=
          (∃ h s, isClientSocketInternal UP _ skt h s clt_addr true ∅ ∅)%I;
        SrvCanListen skt := @isServerSocketInternal Mdl Σ _ _ _ _ _ skt false;
        SrvListens skt := @isServerSocketInternal Mdl Σ _ _ _ _ _ skt true;
        reserved_server_socket_interp := @server_interp _ _ _ _ _ UP; |}.

End Session_Resources_intantiation.

Arguments session_resources_instance {_ _ _ _ _ _ _}.
