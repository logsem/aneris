From stdpp Require Import gmap.
From aneris.examples.crdt.spec Require Import crdt_base crdt_denot crdt_events crdt_time.
From aneris.examples.crdt.statelib.proof Require Import events.
From aneris.examples.crdt.statelib.user_model Require Import semi_join_lattices.
From aneris.examples.crdt.statelib.STS Require Import lst.

(** * Models for state-based CRDTs **)

(* The "state" in "state-based CRDTs" are join semilattices: i.e.
   a poset with a lub operation. *)

Section ModelDef.

  Context `{Op : Type, LatSt: Type,
            !Lattice LatSt, !EqDecision Op, !Countable Op, !CrdtDenot Op LatSt,
            !CRDT_Params}.

  Class StateCrdtModel := {
    (* The lub operation must be coherent with respect to denotations.
       We can assume that s1 and s2 are dep_closed because that is an invariant
       that is always preserved by state-based CRDTs. *)
    st_crdtM_lub_coh : ∀ (s1 s2 : gset (Event Op)) (st1 st2 st3 : LatSt),
      ⟦ s1 ⟧ ⇝ st1 -> ⟦ s2 ⟧ ⇝ st2 ->
      Lst_Validity' s1 -> Lst_Validity' s2 -> Lst_Validity' (s1 ∪ s2) ->
      (∀ (i: nat), fil s1 i ⊆ fil s2 i ∨ fil s2 i ⊆  fil s1 i) ->
      st1 ⊔_l st2 = st3 -> ⟦ s1 ∪ s2 ⟧ ⇝ st3;

    (* The mutator sends a state, an operation, and the replica id where the
       mutation is taking place to a new state.  *)
    st_crdtM_mut: LatSt → Event Op → LatSt → Prop;

    (* All mutations are monotone, so always end up higher up in the lattice.  *)
    st_crdtM_mut_mon (st : LatSt) (e: Event Op) (st': LatSt) :
      st_crdtM_mut st e st' → st ≤_l st';

    (* Mutations are coherent with denotations. *)
    st_crdtM_mut_coh (s : gset (Event Op)) (st st' : LatSt) (ev: Event Op) :
      ⟦ s ⟧ ⇝ st ->
      Lst_Validity' s ->
      ev ∉ s ->
      is_maximum ev (s ∪ {[ ev ]}) ->
      st_crdtM_mut st ev st' -> ⟦ s ∪ {[ ev ]} ⟧ ⇝ st';

    (* The initial CRDT state. *)
    st_crdtM_init_st : LatSt;

    (* The initial state is the denotation of the empty set of operations. *)
    st_crdtM_init_st_coh : ⟦ ∅ ⟧ ⇝ st_crdtM_init_st
  }.

End ModelDef.
Arguments StateCrdtModel (Op LatSt) {_ _ _ _ _}.
