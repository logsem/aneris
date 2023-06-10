From stdpp Require Import list.
From iris.algebra Require Import frac.
From iris.bi.lib Require Import fractional.
From aneris.aneris_lang Require Export resources.
From aneris.examples.reliable_communication.prelude
     Require Import list_minus.
From aneris.examples.snapshot_isolation.specs
     Require Export user_params.

Section Resources.

  Reserved Notation "k ↦ₖ e" (at level 20).

  Inductive local_state : Type :=
   | CanStart
   | Active (ms : gmap Key (option val)) (mc : gmap Key val).

  Class SI_resources Mdl Σ
        `{!anerisG Mdl Σ, !User_params}:= {

    (** System global invariant *)
    GlobalInv : iProp Σ;
    GlobalInvPersistent :> Persistent GlobalInv;

    (** Logical points-to connective *)
    OwnMemKey : Key → option val → iProp Σ
    where "k ↦ₖ v" := (OwnMemKey k v);

    (** Logical points-to connective *)
    ConnectionState : val → local_state → iProp Σ;

    KVS_si : message → iProp Σ;

    (** Properties of points-to connective *)
    OwnMemKey_timeless k v :> Timeless (k ↦ₖ v);
    OwnMemKey_exclusive k v v' :
      k ↦ₖ v ⊢ k ↦ₖ v' -∗ False;

    (** Laws *)

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
