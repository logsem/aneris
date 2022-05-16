From stdpp Require Import base gmap.
From aneris.examples.crdt.spec Require Import crdt_time crdt_events crdt_denot.

(** * Models for state-based CRDTs **)

(* The "state" in "state-based CRDTs" are join semilattices: i.e.
   a poset with a lub operation. *)
Section Lattices.

  Class Lattice (E : Type) := {
    lat_le : relation E;
    lat_po :> PartialOrder lat_le;
    lat_lub : E -> E -> E;
    lat_lub_le : ∀ e1 e2 e3,
        lat_le e1 e3 -> lat_le e2 e3 -> lat_le (lat_lub e1 e2) e3
  }.

End Lattices.

Infix "≤_l" := lat_le (at level 80, no associativity).
Infix "⊔_l" := lat_lub (at level 50, left associativity).

Section ModelDef.

  Context {Op : Type}.
  Context `{!Lattice LatSt, !Log_Time, !EqDecision Op, !Countable Op, !CrdtDenot Op LatSt}.

  (* A set of events is `dep_closed` if it contains every causal dependency of
     every element of the set. *)
  Definition dep_closed (s : gset (Event Op)) : Prop :=
    ∀ e e' : Event Op, e ∈ s -> e' <_t e -> e' ∈ s.

  Lemma dep_closed_union (s s' : gset (Event Op)) :
    dep_closed s -> dep_closed s' -> dep_closed (s ∪ s').
  Proof.
    intros Hsc Hs'c e e' [Hl | Hr]%elem_of_union Hlt.
    - apply elem_of_union_l.
      eapply Hsc; eauto.
    - apply elem_of_union_r.
      eapply Hs'c; eauto.
  Qed.

  Class StateCrdtModel := {
    (* The lub operation must be coherent with respect to denotations.
       We can assume that s1 and s2 are dep_closed because that is an invariant
       that is always preserved by state-based CRDTs. *)
    st_crdtM_lub_coh : ∀ (s1 s2 : gset (Event Op)) (st1 st2 st3 : LatSt),
      ⟦ s1 ⟧ ⇝ st1 ->
      ⟦ s2 ⟧ ⇝ st2 ->
      dep_closed s1 ->
      dep_closed s2 ->
      st1 ⊔_l st2 = st3 <-> ⟦ s1 ∪ s2 ⟧ ⇝ st3;

    (* The mutator sends a state, an operation, and the replica id where the
       mutation is taking place to a new state.  *)
    st_crdtM_mut (st : LatSt) (op : Op) (repId : nat) : LatSt;

    (* All mutations are monotone, so always end up higher up in the lattice.  *)
    st_crdtM_mut_mon (st : LatSt) (op : Op) (repId : nat) :
      st ≤_l (st_crdtM_mut st op repId);

    (* Mutations are coherent with denotations. *)
    st_crdtM_mut_coh (s : gset (Event Op)) (st st' : LatSt) (op : Op) (repId : nat) (ev : (Event Op)) :
      ⟦ s ⟧ ⇝ st ->
      ev.(EV_Op) = op ->
      ev.(EV_Orig) = repId ->
      ev ∉ s ->
      is_maximum ev (s ∪ {[ ev ]}) ->
      st' = st_crdtM_mut st op repId <-> ⟦ s ∪ {[ ev ]} ⟧ ⇝ st';

    (* The initial CRDT state. *)
    st_crdtM_init_st : LatSt;

    (* The initial state is the denotation of the empty set of operations. *)
    st_crdtM_init_st_coh : ⟦ ∅ ⟧ ⇝ st_crdtM_init_st
  }.

End ModelDef.
