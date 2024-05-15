From iris.algebra Require Import gset.
From iris.algebra Require Import frac.
From iris.bi.lib Require Import fractional.
From aneris.aneris_lang Require Export resources.
From aneris.examples.reliable_communication.prelude
     Require Import list_minus.
From aneris.examples.transactional_consistency Require Import user_params aux_defs.

Section Resources.
  Reserved Notation "k ↦ₖ V" (at level 20).
  Reserved Notation "k ↦{ c } vo" (at level 20).

  Class RU_resources Mdl Σ
    `{!anerisG Mdl Σ, !User_params}:= {

    (** System global invariant *)
    GlobalInv : iProp Σ;
    GlobalInv_persistent :> Persistent GlobalInv;

    (** Logical global points-to connective *)
    OwnMemKey : Key → Vals → iProp Σ
    where "k ↦ₖ V" := (OwnMemKey k V);
    OwnMemKey_timeless k V :> Timeless (k ↦ₖ V);

    (** Logical cache points-to connective *)
    OwnLocalKey : Key → val → option val → iProp Σ
    where "k ↦{ c } vo" := (OwnLocalKey k c vo);
    OwnLocalKey_timeless k v c:> Timeless (k ↦{c} v);

    (** Connection state *)
    ConnectionState : val → socket_address → local_state → iProp Σ;
    IsConnected : val → socket_address → iProp Σ;
    IsConnected_persistent c sa :> Persistent (IsConnected c sa);

    (** KVS resources *)
    KVS_ru : message → iProp Σ;
    KVS_Init : iProp Σ;
    KVS_ClientCanConnect : socket_address → iProp Σ;

    (** Seen predciate *)
    Seen : Key → Vals → iProp Σ;
    Seen_timeless k V :> Timeless (Seen k V);
    Seen_persistent k V :> Persistent (Seen k V);

    (** Properties *)
    OwnLocalKey_serializable k cst v :
      k ↦{cst} Some v -∗
      k ↦{cst} Some v ∗ ⌜KVS_Serializable v⌝;

    Seen_valid E k V V' :
      ↑KVS_InvName ⊆ E ->
      GlobalInv ⊢
      Seen k V ∗ k ↦ₖ V' ={E}=∗
      k ↦ₖ V' ∗ ⌜V ⊆ V'⌝;

    Seen_creation E k V :
      ↑KVS_InvName ⊆ E ->
      GlobalInv ⊢
      k ↦ₖ V ={E}=∗
      k ↦ₖ V ∗ Seen k V;

    (** Property of connection *)
    Connection_unique E c c' sa sa' ls ls': 
      ↑KVS_InvName ⊆ E ->
      GlobalInv ⊢
      ConnectionState c sa ls ∗
      ConnectionState c' sa' ls' ={E}=∗
      ConnectionState c sa ls ∗
      ConnectionState c' sa' ls' ∗ ⌜c ≠ c'⌝;
  }.

End Resources.

Notation "k ↦ₖ V" := (OwnMemKey k V) (at level 20).
Notation "k ↦{ c } vo" := (OwnLocalKey k c vo) (at level 20).