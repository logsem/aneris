From Coq Require Import ssreflect.
From stdpp Require Import base gmap.
From aneris.examples.crdt.spec Require Import crdt_time crdt_events.

(** * Denotations for CRDTs *)

Section Denotations.

  (* `Op` is the type of operations embedded in events.
     `St` is the type of (logical) states of the CRDT.
     Events have type `Event` which comes from `Log_Events` below. *)
  Context {Op St : Type}.
  Context `{!Log_Time, !EqDecision Op, !Countable Op}.

  Definition Rel2 (A B : Type) := A -> B -> Prop.

  (* A functional relation *)
  Class Rel2__Fun {A B : Type} (R : Rel2 A B) := {
    rel2_fun : ∀ {a : A} {b b' : B}, R a b -> R a b' -> b = b'
  }.

  (* A CRDT denotation is just a way to give meanings to sets of events.
      The denotation can then serve as a (declarative, high level) specification
      of a CRDT. *)
  Class CrdtDenot := {
    (* A denotation is a relation that relates a set of events to at most one logical
       state. We say at most one because a particular set of events could fail to be
       related to _any_ states at all (because the set of events is invalid). *)
    crdt_denot : Rel2 (gset (Event Op)) St;

    crdt_denot_fun :> Rel2__Fun crdt_denot
  }.

End Denotations.

Arguments CrdtDenot (Op St) {_ _ _}.

Notation "'⟦' s '⟧' '⇝' st" := (crdt_denot s st) (at level 80, no associativity).
