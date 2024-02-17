From iris.algebra Require Import auth gmap excl excl_auth.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code_api.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params.

Definition Hist : Set := list val.

Inductive local_state : Type :=
   | CanStart
   | Active (ms : gmap Key Hist).

Definition can_commit `{User_params}
 (m ms : gmap Key Hist) (mc : gmap Key (option val * bool)) : bool :=
  bool_decide (∀ (k : Key), k ∈ KVS_keys →
  match (mc !! k : option (option val * bool)) with
    | Some (vo, true) => bool_decide (m !! k = ms !! k)
    | _ => true
  end).

Definition commit_event
  (p : option val * bool) (h : Hist) :=
    match p with
    | (Some v, true) => h ++ [v]
    | _              => h
    end.
