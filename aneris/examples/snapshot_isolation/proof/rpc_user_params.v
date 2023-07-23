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
From aneris.examples.snapshot_isolation Require Import snapshot_isolation_code.
From aneris.examples.snapshot_isolation.specs Require Import user_params.
From aneris.examples.snapshot_isolation.proof Require Import
     time events model kvs_serialization.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import resource_algebras server_resources proxy_resources
     global_invariant.

Import gen_heap_light.
Import lock_proof.

Section RPC_user_params.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  (** TODO: Remove it from here once proved and defined.  *)
  Context (list_serialization : serialization → serialization).
  Context (clients : gset socket_address).
  Context  (γKnownClients γGauth γGsnap γT : gname).

  Definition ReqData : Type :=
      (** Read   *) string * nat * (list write_event) +
      (** Start  *) (unit * iProp Σ * (val → iProp Σ) +
      (** Commit *) coPset * nat * (gmap Key val) * iProp Σ * (val → iProp Σ)).

  Definition RepData : Type :=
     (** Read   *) list write_event +
     (** Start  *) (nat +
     (** Commit *) bool).

  Definition ReqPre (reqv : val) (reqd : ReqData) : iProp Σ :=
    Global_Inv clients γKnownClients γGauth γGsnap γT ∗
    (
      (** Read *)
      (
        ∃ k ts h,
          ⌜k ∈ KVS_keys⌝ ∗
          ⌜reqd = inl (k, ts, h)⌝ ∗
          ⌜reqv = InjLV (#(LitString k), #ts)⌝ ∗
          ⌜∀ e, e ∈ h → e.(we_time) < ts⌝ ∗
          ownTimeSnap γT ts ∗
          ownMemSeen γGsnap k h
      )
     ∨
      (** Start *)
      (
       ⌜True⌝ (** TODO *)
      )
     ∨
      (** Commit *)
      (
        ⌜True⌝ (** TODO *)
      )).


  Definition ReqPost
    (repv : val) (reqd : ReqData) (repd : RepData) : iProp Σ :=
    Global_Inv clients γKnownClients γGauth γGsnap γT ∗
    (
      (** Read *)
      (
       (∃ k ts h vo,
           ⌜reqd = inl (k, ts, h)⌝ ∗
           ⌜repd = inl h⌝ ∗
           ⌜repv = InjLV vo⌝ ∗
           ownMemSeen γGsnap k h ∗
           ((⌜vo = NONEV⌝ ∗ ⌜h = []⌝ ) ∨
            (∃ e, ⌜vo = SOMEV (we_val e)⌝ ∗ ⌜hist_to_we h = Some e⌝)))
      )
     ∨
      (** Start *)
      (
       ⌜True⌝ (** TODO *)
      )
     ∨
      (** Commit *)
      (
        ⌜True⌝ (** TODO *)
      )).


  (** TODO: Remove list_serialization from here once proved and defined.  *)
  Global Instance client_handler_at_leader_user_params : MTS_user_params :=
    {|
      MTS_req_ser  := req_serialization list_serialization;
      MTS_req_ser_inj := req_ser_is_injective list_serialization;
      MTS_req_ser_inj_alt := req_ser_is_injective_alt list_serialization;
      MTS_req_data := ReqData;
      MTS_rep_ser  := rep_serialization;
      MTS_rep_ser_inj := rep_ser_is_injective list_serialization;
      MTS_rep_ser_inj_alt := rep_ser_is_injective_alt list_serialization;
      MTS_rep_data := RepData;
      MTS_saddr := KVS_address;
      MTS_mN := (KVS_InvName .@ "server");
      MTS_handler_pre  := ReqPre;
      MTS_handler_post := ReqPost;
    |}.

End RPC_user_params.
