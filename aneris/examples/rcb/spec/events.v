From stdpp Require Import gmap.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import vector_clock_proof.
From aneris.prelude Require Import time.
From aneris.examples.rcb.spec Require Import base.

(** Global and local events *)

Section Events.

  (* TODO: define notation for vc equality, lt, etc... *)

  Class RCB_events :=
    {
      (** Local events *)

      ge : Type;
      GE_payload : ge → val;
      GE_vc : ge -> vector_clock;
      GE_origin : ge -> nat;
      GE_EqDecision :> EqDecision ge;
      GE_Countable :> Countable ge;

      (** Apply events *)

      le : Type;
      LE_payload : le → val;
      LE_vc : le -> vector_clock;
      LE_origin : le -> nat;
      LE_EqDecision :> EqDecision le;
      LE_Countable :> Countable le;

      (** Erasure of local events *)

      erasure : le → ge;
      erasure_payload: ∀ (e : le), (erasure e).(GE_payload) = e.(LE_payload);
      erasure_origin: ∀ (e : le), (erasure e).(GE_origin) = e.(LE_origin);
      erasure_vc: ∀ (e : le), (erasure e).(GE_vc) = e.(LE_vc);
    }.

  (** Aliases for sets of events *)

  Context `{!RCB_events}.

  Notation gstate := (gset ge).
  Notation lstate := (gset le).

  Definition causally_closed : relation lstate :=
    λ s s',
      ∀ le le',
        le ∈ s' → le' ∈ s' →
        vector_clock_lt (LE_vc le) (LE_vc le') →
        le' ∈ s →
        le ∈ s.

  Definition causally_closed_subseteq : relation lstate :=
    λ s s', s ⊆ s' ∧ causally_closed s s'.

  Definition is_ge (v : val) (e : ge) :=
    ∃ p vc o,
      v = ((p, vc), o)%V ∧
      p = (GE_payload e) ∧
      is_vc vc (GE_vc e) ∧
      o = #(GE_origin e).

  Definition is_le (v : val) (a : le) := is_ge v (erasure a).

End Events.

Notation gstate := (gset ge).
Notation lstate := (gset le).


