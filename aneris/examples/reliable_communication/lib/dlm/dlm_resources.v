From iris.algebra Require Import excl.
From trillium.prelude Require Import finitary.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import lock_proof set_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import tactics proofmode.
From actris.channel Require Export proto.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.examples.reliable_communication Require Import user_params.
From aneris.examples.reliable_communication.spec Require Import resources proofmode api_spec.
From aneris.examples.reliable_communication.lib.dlm
     Require Import dlm_code dlm_prelude.

(** Definition of the distribued lock protocol. *)

Section DL_protocol.
  Context `{!anerisG Mdl Σ}.
  Context (R : iProp Σ).
  Context (dl_locked_internal : iProp Σ).
  (* Context (dl_locked_exclusive : dl_locked -∗ dl_locked -∗ False). *)

Definition dlock_protocol_aux (rec : string -d> iProto Σ) : string -d> iProto Σ :=
    λ s,
      let rec : string -d> iProto Σ := rec in
      (<!> MSG #s {{ (⌜s = "acquire"⌝) ∨ (⌜s = "release"⌝ ∗ (dl_locked_internal ∗ R)) }} ;
      if bool_decide (s = "acquire")
       then
         (<?> MSG #"acquire_OK" {{ (dl_locked_internal ∗ R) }};
          rec "release")
       else (rec "acquire"))%proto.

  Global Instance dlock_protocol_aux_contractive : Contractive dlock_protocol_aux.
  Proof. solve_proper_prepare. f_equiv; solve_proto_contractive. Qed.
  Definition dlock_protocol := fixpoint (dlock_protocol_aux).
  Global Instance dlock_protocol_unfold s :
    ProtoUnfold (dlock_protocol s) (dlock_protocol_aux dlock_protocol s).
  Proof. apply proto_unfold_eq, (fixpoint_unfold dlock_protocol_aux). Qed.

End DL_protocol.

(** Definition and realization of resources *)

Class DlockG Σ := LockG { Dlock_tokG :> inG Σ (exclR unitO) }.
Definition DlockΣ : gFunctors := #[GFunctor (exclR unitO)].

Import lock_proof.
Global Instance subG_DlockΣ {Σ} : subG DlockΣ Σ → DlockG Σ.
Proof. solve_inG. Qed.

Section DL_resources_definition.
  Context `{!anerisG Mdl Σ, !@Chan_mapsto_resource Σ, !DL_params, !DlockG Σ, !lockG Σ}.
  Context (γdlk : gname).
  Context (dl_locked_internal : iProp Σ).
  Context (dl_locked_internal_exclusive : dl_locked_internal -∗ dl_locked_internal -∗ False).
  Context (R : iProp Σ).

  Definition dlock_protocol_internal (s : string) : iProto Σ :=
  dlock_protocol dl_locked_internal R s.

  Definition DLockCanAcquire_internal (sa : socket_address) (c : val) : iProp Σ :=
    c ↣{ ip_of_address sa, string_serialization } (dlock_protocol_internal "acquire").

  Definition DLockCanRelease_internal (sa : socket_address) (c : val) : iProp Σ :=
    c ↣{ ip_of_address sa, string_serialization } (dlock_protocol_internal "release").

  Definition server_resources_at_chan ip (γdlk : gname) (c : val) s : iProp Σ :=
      (⌜s = "acquire"⌝ ∨ (⌜s = "release"⌝ ∗ dl_locked_internal ∗ locked γdlk)) ∗
        c ↣{ ip, string_serialization } (iProto_dual (dlock_protocol_internal s)).

  Definition dlock_server_inv ip (γdlk : gname) (cl : list val) : iProp Σ :=
    ([∗ list] c ∈ cl, ∃ s, server_resources_at_chan ip γdlk c s).

  Definition is_dlock_internal_server_is_lock ip γdlk lk cl : iProp Σ :=
    is_lock ip γdlk lk (dlock_server_inv ip γdlk cl).

End DL_resources_definition.

(*
Class DL_resources_internal `{!anerisG Mdl Σ, !DL_params} := {
    DLR_locked : iProp Σ;
    DLR_locked_exclusive : DLR_locked -∗ DLR_locked -∗ False;
    DLR_locked_timeless : Timeless (DLR_locked);
    DLR_UP :> Reliable_communication_service_params;
    DLR_addr : DLR_UP.(RCParams_srv_saddr) = DL_server_addr;
    DLR_namespace : DLR_UP.(RCParams_srv_N) = DL_namespace;
    DLR_clt_ser : DLR_UP.(RCParams_clt_ser) = string_serialization;
    DLR_srv_ser : DLR_UP.(RCParams_srv_ser) = string_serialization;
    DLR_proto :  RCParams_protocol = dlock_protocol_internal DLR_locked R "acquire";
    DLR_ChanMapstoRes :> @Chan_mapsto_resource Σ;
    DLR_SessionRes :> SessionResources DLR_UP;
    DLR_Session :> Reliable_communication_Specified_API_session DLR_ChanMapstoRes;
    DLR_Network :> Reliable_communication_Specified_API_network DLR_UP DLR_SessionRes;
}.
*)
