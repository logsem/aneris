From stdpp Require Import list.
From iris.algebra Require Import frac.
From iris.bi.lib Require Import fractional.
From aneris.aneris_lang Require Export resources.
From aneris.examples.reliable_communication.prelude
     Require Import list_minus.
From aneris.examples.snapshot_isolation.specs
     Require Export user_params.

Definition TObj : Set := (socket_address * gmap Key val).
Definition THst : Set := list TObj.

Definition at_origin (sa : socket_address) (h : THst) : THst :=
  filter (λ x, fst x = sa) h.

Definition can_commit (h : THst) (s : gmap Key val) (h' : THst) :=
  ∀ (s' : TObj), s' ∈ list_minus h' h → dom s ## dom s'.2.

Fixpoint get_val_at_key (h : THst) (k : Key) : option val :=
 match h with
 | [] => None
 | t :: h' =>
     match t.2 !! k with
       | None => get_val_at_key h' k
       | Some v => Some v
     end
 end.

Definition get_current_state (h : THst) : gmap Key val :=
  fold_right
    (fun (mi : TObj) (m : gmap Key val) =>
       merge (fun voi vo => if bool_decide (voi = None) then vo else voi)
             mi.2 m) ∅ h.

Lemma get_value_at_key_coh (h : THst) (k : Key) :
  get_val_at_key h k = get_current_state h !! k.
Proof. Admitted.

Notation "h ≤ₚ h'" := (h `prefix_of` h') (at level 20).


(** The idea of resources as predicates:

GHist, Global Transaction History       :  [T0 T1 ... Ti ... T45 ... Tn]
LHist, Local Client sa1 History         :  [   T1            T45]
LHist, Local Client sa2 History         :  [T0        Ti]
TState, Current Client sa1 T(n+1) state :  snapshot = Tn; cache={|k1 ↦ v1; ...|}

*)

Section Resources.

  Class SI_resources Mdl Σ `{!anerisG Mdl Σ, !User_params}:= {

    (** System global invariant *)
    GlobalInv : iProp Σ;
    GlobalInvPersistent :> Persistent GlobalInv;

    (** Global history of committed transactions *)
    GHist : THst → iProp Σ;

    (** Local history of committed transactions *)
    LHist : val → socket_address → THst → iProp Σ;

    (** Local State of the current transaction containing the snapshot
        and the effects of writes *)
    TState : val → THst → gmap Key val → iProp Σ;

    CanStart : socket_address → val → iProp Σ;

    KVS_si : message → iProp Σ;

    (** Laws *)
    GHist_exclusive h h' :
      GHist h ⊢ GHist h' -∗ False;

    LHist_exclusive r sa h h' :
      LHist r sa h ⊢ LHist r sa h' -∗ False;

    LHist_origin r sa h :
      LHist r sa h ⊢ ⌜∀ s, s ∈ h → s.1 = sa⌝;

    TState_exclusive r h h' m m' :
      TState r h m ⊢ TState r h' m' -∗ False;

    GHist_LHist_relation E r sa h h' :
    ↑KVS_InvName ⊆ E ->
    GlobalInv ⊢ LHist r sa h -∗ GHist h' ={E}=∗
    ⌜at_origin sa h' = h⌝;

    GHist_Keys E h :
    ↑KVS_InvName ⊆ E ->
      GlobalInv ⊢ GHist h ={E}=∗
      ⌜∀ s, s ∈ h → dom s.2 ⊆ KVS_keys⌝;

    LHist_Keys E r sa h :
    ↑KVS_InvName ⊆ E ->
      GlobalInv ⊢ LHist r sa h ={E}=∗
      ⌜∀ s, s ∈ h → dom s.2 ⊆ KVS_keys⌝;

    TState_Keys E r h m :
    ↑KVS_InvName ⊆ E ->
      GlobalInv ⊢ TState r h m ={E}=∗ ⌜dom m ⊆ KVS_keys⌝;

    (* This law is probably not needed. *)
    (* GHist_LState_relation E rpc h h' s :
    ↑KVS_InvName ⊆ E ->
    GlobalInv ⊢ TState rpc h' s -∗ GHist h ={E}=∗
    ⌜h ≤ₚ h'⌝; *)

   }.

End Resources.

(* Arguments SI_resources _ _ : clear implicits. *)
