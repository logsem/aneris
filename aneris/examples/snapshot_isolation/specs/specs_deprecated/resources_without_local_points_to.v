From stdpp Require Import list.
From iris.algebra Require Import frac.
From iris.bi.lib Require Import fractional.
From aneris.aneris_lang Require Export resources.
From aneris.examples.reliable_communication.prelude
     Require Import list_minus.
From aneris.examples.snapshot_isolation.specs
     Require Export user_params.
From aneris.examples.snapshot_isolation.specs.specs_deprecated
     Require Export time events.
     
Section Resources.

  Reserved Notation "k ↦ₖ e" (at level 20).

  Inductive local_state `{!KVS_time}: Type :=
   | CanStart
   | Active (ms : gmap Key (option write_event)) (mc : gmap Key val).

  Class SI_resources Mdl Σ
        `{!anerisG Mdl Σ, !KVS_time, !User_params}:= {

    (** System global invariant *)
    GlobalInv : iProp Σ;
    GlobalInvPersistent :> Persistent GlobalInv;

    (** Logical points-to connective *)
    OwnMemKey : Key → option write_event → iProp Σ
    where "k ↦ₖ v" := (OwnMemKey k v);

    (** Logical points-to connective *)
    ConnectionState : val → local_state → iProp Σ;

    KVS_si : message → iProp Σ;

    (** Properties of points-to connective *)
    OwnMemKey_timeless k v :> Timeless (k ↦ₖ v);
    OwnMemKey_exclusive k v v' :
      k ↦ₖ v ⊢ k ↦ₖ v' -∗ False;
    OwnMemKey_key k write_event E :
      nclose KVS_InvName ⊆ E →
      GlobalInv ⊢
      k ↦ₖ Some write_event ={E}=∗
      k ↦ₖ Some write_event ∗ ⌜we_key write_event = k⌝;

    (** Laws *)
    ConnectionState_relation E k r ms mc write_event :
    ↑KVS_InvName ⊆ E ->
    GlobalInv ⊢
    ConnectionState r (Active ms mc) -∗ k ↦ₖ Some write_event ={E}=∗
    ⌜k ∈ dom ms →
    ∀ write_event', ms !! k = Some (Some write_event') → write_event' ≤ₜ write_event ⌝;

    ConnectionState_Keys E r ms mc :
    ↑KVS_InvName ⊆ E ->
      GlobalInv ⊢
      ConnectionState r (Active ms mc) ={E}=∗
      ⌜dom ms ⊆ KVS_keys⌝ ∧ ⌜dom mc ⊆ dom ms⌝;

  (* ... about keys in domains *)
  }.

End Resources.
(* Arguments SI_resources _ _ : clear implicits. *)

Notation "k ↦ₖ v" := (OwnMemKey k v) (at level 20).
