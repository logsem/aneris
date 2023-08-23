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

Definition can_commit_transaction `{User_params}
 (m ms : gmap Key (list write_event))
 (mc : gmap Key (option val * bool)) : bool :=
  bool_decide
    (∀ (k : Key), k ∈ KVS_keys →
                  match ((mc !! k) : option ((option val) * bool)) with
                  | Some (vo, true) => bool_decide (m !! k = ms !! k)
                  | Some (_, false) => true
                  | None => true
                  end).

Definition commit_write_event
  (p : option val * bool) (h : list write_event) (ct : nat) (k : Key) :=
    match p with
    | (Some v, true) => h ++ [{| we_key := k; we_val := v; we_time := ct|}]
    | _              => h
    end.

Section RPC_user_params.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  (** TODO: Remove it from here once proved and defined.  *)
  Context (clients : gset socket_address).
  Context  (γKnownClients γGauth γGsnap γT : gname).

  Definition ReqData : Type :=
      (** Read   *) string * nat * (list write_event) +
      (** Start  *) (coPset * iProp Σ * (val → iProp Σ) +
      (** Commit *) (coPset * nat *
                    (gmap Key val) *
                    (gmap Key (option val * bool))) *
                    (gmap Key (list write_event)) * iProp Σ * (val → iProp Σ)).

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
        ∃ E P Q,
          ⌜reqd = inr (inl (E, P, Q))⌝ ∗
          ⌜reqv = InjRV (InjLV (#()))%V⌝ ∗
          ⌜↑KVS_InvName ⊆ E⌝ ∗
          P ∗
          (P
           ={⊤, E}=∗
           (∃ m, ([∗ map] k ↦ h ∈ m, ownMemUser γGauth γGsnap k h) ∗
                 ▷ (∀ ts,
                      ownTimeSnap γT ts ∗
                      ([∗ map] k ↦ h ∈ m,
                         ownMemUser γGauth γGsnap k h ∗
                         ⌜∀ e, e ∈ h → e.(we_time) < ts⌝)
                      ={E,⊤}=∗ Q #ts))
          )
      )
     ∨
      (** Commit *)
      (
        ∃ E P Q cmapV
          (cache_updatesM : gmap Key val)
          (cache_logicalM : gmap Key (option val * bool))
          (Msnap : gmap Key (list write_event))
          (ts : nat),
          ⌜reqd = inr (inr (E, ts, cache_updatesM, cache_logicalM, Msnap, P, Q))⌝ ∗
          ⌜reqv = InjRV (InjRV (#ts, cmapV))%V⌝ ∗
          ⌜↑KVS_InvName ⊆ E⌝ ∗
          ⌜is_map cmapV cache_updatesM⌝ ∗
          ⌜is_coherent_cache cache_updatesM cache_logicalM Msnap⌝ ∗
          P ∗
         (P ={⊤, E}=∗
          ∃ (m : gmap Key (list write_event)),
          ⌜dom m = dom Msnap⌝ ∗
          ownTimeSnap γT ts ∗
          ([∗ map] k ↦ h' ∈ Msnap,
             ownMemSeen γGsnap k h' ∗
             ⌜∀ e, e ∈ h' → e.(we_time) < ts⌝) ∗
          ([∗ map] k ↦ h ∈ m, ownMemUser γGauth γGsnap k h) ∗
           ▷ (∀ (ct : nat) (b : bool),
                ((** Transaction has been commited. *)
                 (⌜b = true⌝ ∗ ⌜can_commit_transaction m Msnap cache_logicalM⌝ ∗
                 ([∗ map] k↦ h;p ∈ m; cache_logicalM,
                  ownMemUser γGauth γGsnap k (commit_write_event p h ct k) ∗
                    ownMemSeen γGsnap k (commit_write_event p h ct k))) ∨
                 (** Transaction has been aborted. *)
                 (⌜b = false⌝ ∗ ⌜¬ can_commit_transaction m Msnap cache_logicalM⌝ ∗
                    [∗ map] k ↦ h ∈ m,
                    ownMemUser γGauth γGsnap k h ∗
                    ownMemSeen γGsnap k h)) ={E,⊤}=∗
                Q #b)
         )
      )).
  Definition ReqPost
    (repv : val) (reqd : ReqData) (repd : RepData) : iProp Σ :=
    Global_Inv clients γKnownClients γGauth γGsnap γT ∗
    (
      (** Read *)
      (
       ∃ k ts h vo,
           ⌜reqd = inl (k, ts, h)⌝ ∗
           ⌜repd = inl h⌝ ∗
           ⌜repv = InjLV vo⌝ ∗
           ownMemSeen γGsnap k h ∗
           ((⌜vo = NONEV⌝ ∗ ⌜h = []⌝ ) ∨
            (∃ e, ⌜vo = SOMEV (we_val e)⌝ ∗ ⌜hist_to_we h = Some e⌝))
      )
     ∨
      (** Start *)
      (
         ∃ E P Q ts,
          ⌜reqd = inr (inl (E, P, Q))⌝ ∗
          ⌜repd = inr (inl ts)⌝ ∗
          ⌜repv = InjRV (InjLV #ts)⌝ ∗
          Q #ts
      )
     ∨
      (** Commit *)
      (
        ∃ E P Q
          (cache_updatesM : gmap Key val)
          (cache_logicalM : gmap Key (option val * bool))
          (Msnap : gmap Key (list write_event))
          (ts : nat) (b : bool),
          ⌜reqd = inr (inr (E, ts, cache_updatesM, cache_logicalM, Msnap, P, Q))⌝ ∗
          ⌜repd = inr (inr b)⌝ ∗
          ⌜repv = InjRV (InjRV #b)⌝ ∗
          Q #b
      )).

  (** TODO: Remove list_serialization from here once proved and defined.  *)
  Global Instance client_handler_rpc_user_params : MTS_user_params :=
    {|
      MTS_req_ser  := req_serialization;
      MTS_req_ser_inj := req_ser_is_injective;
      MTS_req_ser_inj_alt := req_ser_is_injective_alt;
      MTS_req_data := ReqData;
      MTS_rep_ser  := rep_serialization;
      MTS_rep_ser_inj := rep_ser_is_injective;
      MTS_rep_ser_inj_alt := rep_ser_is_injective_alt;
      MTS_rep_data := RepData;
      MTS_saddr := KVS_address;
      MTS_mN := (KVS_InvName .@ "server");
      MTS_handler_pre  := ReqPre;
      MTS_handler_post := ReqPost;
    |}.

End RPC_user_params.