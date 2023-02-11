From aneris.aneris_lang Require Import resources proofmode.
From aneris.prelude Require Import time.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events.

(** * Iris resources for client reasoning about CRDTs *)

Section Resources.
  Context `{!anerisG Mdl Σ, !CRDT_Params, !Log_Time,
            !EqDecision CRDT_Op, !Countable CRDT_Op}.

  Class CRDT_Res_Mixin := {
    (** * Ghost resources *)
    (* Global invariant *)
    GlobInv : iProp Σ;
    GlobInv_persistent :> Persistent GlobInv;

    (* Global state *)
    GlobState : event_set CRDT_Op → iProp Σ;
    GlobState_Exclusive s s' : GlobState s ⊢ GlobState s' -∗ False;
    GlobState_Timeless s :> Timeless (GlobState s);

    (* Global state snapshot *)
    GlobSnap : event_set CRDT_Op → iProp Σ;
    GlobSnap_Timeless s :> Timeless (GlobSnap s);
    GlobSnap_Persistent s :> Persistent (GlobSnap s);

    (* Local state. The resource LocState i s s' records the fact
       that locally (at node i) we have performed:
         1) _exactly_ the operations in `own`, which originate at
            node i.
         2) _at least_ the operations in `foreign`, which originate
            outside of node i.
       That is, we split events into "own" and "foreign" sets, and
       we have precise knowledge of the former, but not of the latter. *)
    LocState (repId : nat) (own foreign : event_set CRDT_Op) : iProp Σ;
    LocState_Timeless i s s' :> Timeless (LocState i s s');
    LocState_Exclusive i s1 s2 s1' s2' : LocState i s1 s2 ⊢ LocState i s1' s2' -∗ False;

    (* Local state snapshot *)
    LocSnap (repId : nat) (own foreign : event_set CRDT_Op) : iProp Σ;
    LocSnap_Timeless i s s' :> Timeless (LocSnap i s s');
    LocSnap_Persistent i s1 s2 :> Persistent (LocSnap i s1 s2);

    (** * Laws about global state only *)
    GlobState_TakeSnap E s :
      ↑CRDT_InvName ⊆ E ->
      GlobInv ⊢
      GlobState s ={E}=∗ GlobState s ∗ GlobSnap s;

    GlobSnap_Union s s' : GlobSnap s ⊢ GlobSnap s' -∗ GlobSnap (s ∪ s');

    GlobSnap_GlobState_Included E s s' :
      ↑CRDT_InvName ⊆ E ->
      GlobInv ⊢
      GlobSnap s -∗ GlobState s' ={E}=∗ ⌜s ⊆ s'⌝ ∗ GlobState s';

    GlobSnap_Ext E s s' :
      ↑CRDT_InvName ⊆ E ->
      GlobInv ⊢
      GlobSnap s -∗ GlobSnap s' ={E}=∗
      ⌜∀ e e', e ∈ s -> e' ∈ s' -> e =_t e' -> e = e'⌝;

    GlobSnap_TotalOrder E s :
      ↑CRDT_InvName ⊆ E ->
      GlobInv ⊢ GlobSnap s ={E}=∗ ⌜events_total_order s⌝;

    (** * Laws about local state only *)
    LocState_OwnOrig i s1 s2 : LocState i s1 s2 ⊢ ⌜∀ e, e ∈ s1 -> e.(EV_Orig) = i⌝;
    LocState_ForeignOrig i s1 s2 : LocState i s1 s2 ⊢ ⌜∀ e, e ∈ s2 -> ¬ (e.(EV_Orig) = i)⌝;

    LocSnap_OwnOrig i s1 s2 : LocSnap i s1 s2 ⊢ ⌜∀ e, e ∈ s1 -> e.(EV_Orig) = i⌝;
    LocSnap_ForeignOrig i s1 s2 : LocSnap i s1 s2 ⊢ ⌜∀ e, e ∈ s2 -> ¬ (e.(EV_Orig) = i)⌝;

    LocState_TakeSnap i s s' : LocState i s s' ⊢ LocState i s s' ∗ LocSnap i s s';

    LocSnap_Union E i s1 s2 s1' s2' :
      ↑CRDT_InvName ⊆ E ->
      GlobInv ⊢
      LocSnap i s1 s2 -∗ LocSnap i s1' s2' ={E}=∗ LocSnap i (s1 ∪ s1') (s2 ∪ s2');

    (* Notice that we get causality in addition to set inclusion *)
    LocSnap_LocState_Included_CC E i s1 s2 s1' s2' :
      ↑CRDT_InvName ⊆ E ->
      GlobInv ⊢
              LocSnap i s1 s2 -∗ LocState i s1' s2' ={E}=∗
              ⌜s1 ∪ s2 ⊆_cc s1' ∪ s2'⌝ ∗ LocState i s1' s2';

    LocSnap_Ext E i i' s1 s2 s1' s2' :
      ↑CRDT_InvName ⊆ E ->
      GlobInv ⊢
      LocSnap i s1 s2 -∗ LocSnap i' s1' s2' ={E}=∗
      ⌜∀ e e', e ∈ s1 ∪ s2 -> e' ∈ s1' ∪ s2' -> e =_t e' -> e = e'⌝;

    LocSnap_EV_Orig E i s1 s2 :
      ↑CRDT_InvName ⊆ E ->
      GlobInv ⊢
      LocSnap i s1 s2 ={E}=∗
      ⌜∀ e, e ∈ s1 ∪ s2 → e.(EV_Orig) < length CRDT_Addresses⌝;

    (** * Laws that connect local and global state *)

    (* All local events have been recorded globally *)
    LocSnap_GlobSnap_Provenance E i s1 s2 e :
      ↑CRDT_InvName ⊆ E →
      e ∈ s1 ∪ s2 →
      GlobInv ⊢
      LocSnap i s1 s2 ={E}=∗ ∃ h, GlobSnap h ∗ ⌜e ∈ h⌝;

    (* Events recorded globally as coming from an origin `i` do
       in fact originate there *)
    LocState_GlobSnap_Provenance E i s1 s2 h :
      ↑CRDT_InvName ⊆ E ->
      GlobInv ⊢
      LocState i s1 s2 -∗
      GlobSnap h ={E}=∗
        LocState i s1 s2 ∗ ⌜∀ e, e ∈ h -> e.(EV_Orig) = i -> e ∈ s1⌝;

    (* Events are received locally in causal order *)
    LocState_GlobSnap_Causality E i s1 s2 h :
      ↑CRDT_InvName ⊆ E →
      GlobInv ⊢
      LocState i s1 s2 -∗ GlobSnap h ={E}=∗
        LocState i s1 s2 ∗
        ⌜∀ a e, a ∈ h → e ∈ s1 ∪ s2 → a <_t e → a ∈ s1 ∪ s2⌝;
  }.

End Resources.

Global Arguments CRDT_Res_Mixin _ _ {_ _ _} (CRDT_Op) {_ _}.
