From stdpp Require Import list.
From iris.algebra Require Import frac.
From iris.bi.lib Require Import fractional.
From aneris.aneris_lang Require Export resources.
From aneris.examples.reliable_communication.prelude
     Require Import list_minus.
From aneris.examples.transactional_consistency.snapshot_isolation.specs
     Require Import aux_defs.
From aneris.examples.transactional_consistency Require Import user_params.

Notation "h ≤ₚ h'" := (h `prefix_of` h') (at level 20).

Section Resources.

  Reserved Notation "k ↦ₖ h" (at level 20).
  Reserved Notation "k ↦{ c } vo" (at level 20).

  Class SI_resources Mdl Σ
    `{!anerisG Mdl Σ, !User_params}:= {

    (** System global invariant *)
    GlobalInv : iProp Σ;
    GlobalInv_persistent :> Persistent GlobalInv;

    (** Logical global points-to connective *)
    OwnMemKey : Key → Hist → iProp Σ
    where "k ↦ₖ h" := (OwnMemKey k h);
    OwnMemKey_timeless k h :> Timeless (k ↦ₖ h);

    (** Logical cache points-to connective *)
    OwnLocalKey : Key → val → option val → iProp Σ
    where "k ↦{ c } vo" := (OwnLocalKey k c vo);
    OwnLocalKey_timeless k v c:> Timeless (k ↦{c} v);

    (** Connection state *)
    ConnectionState : val → socket_address → local_state → iProp Σ;
    IsConnected : val → socket_address → iProp Σ;
    IsConnected_persistent c sa :> Persistent (IsConnected c sa);

    (** KVS resources *)
    KVS_si : message → iProp Σ;
    KVS_Init : iProp Σ;
    KVS_ClientCanConnect : socket_address → iProp Σ;

    (** Cache Key Status *)
    KeyUpdStatus : val → Key → bool → iProp Σ;

    (** Seen predciate *)
    Seen : Key → Hist → iProp Σ;
    Seen_timeless k h :> Timeless (Seen k h);
    Seen_persistent k h :> Persistent (Seen k h);

    (** Properties of points-to connective *)
    OwnLocalKey_serializable k cst v :
      k ↦{cst} Some v -∗
      k ↦{cst} Some v ∗ ⌜KVS_Serializable v⌝;

    Seen_valid E k h h' :
      ↑KVS_InvName ⊆ E ->
      GlobalInv ⊢
      Seen k h ∗ k ↦ₖ h' ={E}=∗
      k ↦ₖ h' ∗ ⌜h ≤ₚ h'⌝;

    Seen_creation E k h :
      ↑KVS_InvName ⊆ E ->
      GlobalInv ⊢
      k ↦ₖ h ={E}=∗
      k ↦ₖ h ∗ Seen k h;
  }.

End Resources.
(* Arguments SI_resources _ _ : clear implicits. *)

Notation "k ↦ₖ h" := (OwnMemKey k h) (at level 20).
Notation "k ↦{ c } vo" := (OwnLocalKey k c vo) (at level 20).
