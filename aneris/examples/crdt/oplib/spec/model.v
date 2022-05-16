From Coq Require Import ssreflect.
From stdpp Require Import base gmap.
From aneris.examples.crdt.spec Require Import crdt_time crdt_events crdt_denot.

Section ModelDef.

  Context {Op St : Type}.
  Context `{!Log_Time, !EqDecision Op, !Countable Op, !CrdtDenot Op St}.

  (**  Captures what it means for an effect function of an op-based CRDT to
       be "coherent" with the CRDT's denotation.
       We can assume that the new event `e` has not been seen before and,
       furthermore, it is maximal w.r.t all other events.
       This models the fact that events are communicated in causal order. *)
  Class OpCrdtEffectCoh (effect : St -> Event Op -> St -> Prop) :=
    op_crdt_effect_coh : ∀ (s : gset (Event Op)) (e : Event Op) (st st' : St),
      ⟦ s ⟧ ⇝ st ->
      e ∉ s ->
      maximal e (s ∪ {[ e ]}) ->
      events_ext (s ∪ {[ e ]}) ->
      events_total_order (s ∪ {[ e ]}) ->
      effect st e st' <-> ⟦ s ∪ {[ e ]} ⟧ ⇝ st'.

  (** Model of a causal op-based CRDT
      Here's one way to think of the model: a CRDT is specified
      with a labelled-transition system that satisfies some additional properties:
      - there's a single initial state
      - there's a transition function called `effect` that takes a
        (state, event) pair to at most another state (if there's no target
        state then this models an error/unexpected event)
      - the effect relation is coherent with respect to the CRDT's denotation.
        This is where causality shows up in one the assumptions of coherence.
      - the initial state is the result of taking the denotation of the empty
        set of events
   *)
  Class OpCrdtModel := {
    (** The effect relation connects a (state, event) pair to another state *)
    op_crdtM_effect : St -> Event Op -> St -> Prop;

    (** ... but there can be at most one target state *)
    op_crdtM_effect_fun st : Rel2__Fun (op_crdtM_effect st);

    op_crdtM_effect_coh :> OpCrdtEffectCoh op_crdtM_effect;

    (** The initial state *)
    op_crdtM_init_st : St;

    (** ... which is the denotation of the empty set of events *)
    op_crdtM_init_st_coh : ⟦ ∅ ⟧ ⇝ op_crdtM_init_st;
  }.

End ModelDef.

Arguments OpCrdtModel (Op St) {_ _ _ _}.

Notation "st '-{' ev '}->' st'" := (op_crdtM_effect st ev st') (at level 100, no associativity).
