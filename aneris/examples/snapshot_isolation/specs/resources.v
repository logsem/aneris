From stdpp Require Import list.
From iris.algebra Require Import frac.
From iris.bi.lib Require Import fractional.
From aneris.aneris_lang Require Export resources.
From aneris.examples.reliable_communication.prelude
     Require Import list_minus.
From aneris.examples.snapshot_isolation.specs
     Require Export user_params time events.

Section Resources.

  Reserved Notation "k ↦ₖ e" (at level 20).

  Inductive local_state `{!KVS_time}: Type :=
   | CanStart
   | Active (ms : gmap Key (option we)) (mc : gmap Key val).

  Class SI_resources Mdl Σ
        `{!anerisG Mdl Σ, !KVS_time, !User_params}:= {

    (** System global invariant *)
    GlobalInv : iProp Σ;
    GlobalInvPersistent :> Persistent GlobalInv;

    (** Logical points-to connective *)
    OwnMemKey : Key → option we → iProp Σ
    where "k ↦ₖ v" := (OwnMemKey k v);

    (** Logical points-to connective *)
    ConnectionState : val → local_state → iProp Σ;

    KVS_si : message → iProp Σ;

    (** Properties of points-to connective *)
    OwnMemKey_timeless k v :> Timeless (k ↦ₖ v);
    OwnMemKey_exclusive k v v' :
      k ↦ₖ v ⊢ k ↦ₖ v' -∗ False;
    OwnMemKey_fractional k v :>
      Fractional (λ q, k ↦ₖ v);
    OwnMemKey_as_fractional k q v :>
      AsFractional (k ↦ₖ v) (λ q, k ↦ₖ v) q ;
    OwnMemKey_key k we E :
      nclose KVS_InvName ⊆ E →
      GlobalInv ⊢
      k ↦ₖ Some we ={E}=∗
      k ↦ₖ Some we ∗ ⌜we_key we = k⌝;

    (** Laws *)
    ConnectionState_relation E k r ms mc we :
    ↑KVS_InvName ⊆ E ->
    GlobalInv ⊢
    ConnectionState r (Active ms mc) -∗ k ↦ₖ Some we ={E}=∗
    ⌜k ∈ dom ms →
    ∀ we', ms !! k = Some (Some we') → we' ≤ₜ we ⌝;

    ConnectionState_Keys E r ms mc :
    ↑KVS_InvName ⊆ E ->
      GlobalInv ⊢
      ConnectionState r (Active ms mc) ={E}=∗
      ⌜dom ms ⊆ KVS_keys⌝ ∧ ⌜dom mc ⊆ dom ms⌝;

  (* ... about keys in domains *)
  }.

End Resources.
(* Arguments SI_resources _ _ : clear implicits. *)

Notation "k ↦ₖ v" := (OwnMemKey k 1 v) (at level 20).
