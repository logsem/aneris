From stdpp Require Import base gmap.
From aneris.examples.crdt.spec Require Import crdt_denot crdt_events crdt_time.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.proof Require Import events.

(** * Models for state-based CRDTs **)

(* The "state" in "state-based CRDTs" are join semilattices: i.e.
   a poset with a lub operation. *)
Section Lattices.

  Class Lattice (E : Type) := {
    lat_le : relation E;
    lat_po :> PartialOrder lat_le;
    lat_lub : E -> E -> E;
    lat_lub_spec :
      ∀ e1 e2,
        lat_le e1 (lat_lub e1 e2)
          ∧ lat_le e2 (lat_lub e1 e2)
          ∧ ∀ e, lat_le e1 e → lat_le e2 e → lat_le (lat_lub e1 e2) e;
  }.

  (** Properties on the least upper bound *)
  Lemma lat_lub_idem {E: Type} (L: Lattice E) (e: E) :
    lat_lub e e = e.
  Proof.
    destruct lat_po as [[_ _] Ha].
    destruct (lat_lub_spec e e) as (Hle1 & Hle2 & Hsp).
    apply Ha; last assumption.
    by apply Hsp.
  Qed.
  Lemma lat_lub_comm {E: Type} (L: Lattice E) (e e': E) :
    lat_lub e e' = lat_lub e' e.
  Proof.
    destruct lat_po as [[_ _] Ha].
    destruct (lat_lub_spec e e') as (Hle1 & Hle2 & Hsp).
    destruct (lat_lub_spec e' e) as (Hle1' & Hle2' & Hsp').
    apply Ha.
    - by apply Hsp.
    - by apply Hsp'.
  Qed.

  Lemma lat_lub_le_l {E: Type} (L: Lattice E) (e e' e'': E):
    lat_le e'' e → lat_le e'' (lat_lub e e').
  Proof.
    destruct lat_po as [[_ Rt] _].
    destruct (lat_lub_spec e e') as (A & B & C).
    intros Hle.
    by apply (Rt e'' e (lat_lub e e')).
  Qed.
  Lemma lat_lub_le_r {E: Type} (L: Lattice E) (e e' e'': E):
    lat_le e'' e' → lat_le e'' (lat_lub e e').
  Proof.
    destruct lat_po as [[_ Rt] _].
    destruct (lat_lub_spec e e') as (A & B & C).
    intros Hle.
    by apply (Rt e'' e' (lat_lub e e')).
  Qed.

  Lemma lat_lub_assoc {E: Type} (L: Lattice E) (e e' e'': E) :
    lat_lub e (lat_lub e' e'') = lat_lub (lat_lub e e') e''.
  Proof.
    destruct lat_po as [[_ _] Ha].
    apply Ha.
    - destruct (lat_lub_spec e (lat_lub e' e'')) as (Hubl & Hubr & Hleast).
      apply Hleast.
      + by do 2 apply lat_lub_le_l.
      + destruct (lat_lub_spec e' e'') as (Hubl' & Hubr' & Hleast').
        apply (Hleast' (lat_lub (lat_lub e e') e'')).
        * by apply lat_lub_le_l, lat_lub_le_r.
        * by apply lat_lub_le_r.
    - destruct (lat_lub_spec (lat_lub e e') e'') as (Hubl & Hubr & Hleast).
      apply Hleast.
      + destruct (lat_lub_spec e e') as (Hubl' & Hubr' & Hleast').
        apply Hleast'.
        * by apply lat_lub_le_l.
        * by apply lat_lub_le_r, lat_lub_le_l.
      + by do 2 apply lat_lub_le_r.
  Qed.
End Lattices.

Infix "≤_l" := lat_le (at level 80, no associativity).
Infix "⊔_l" := lat_lub (at level 50, left associativity).

Section ModelDef.

  Context {Op : Type} {LatSt: Type}.
  Context `{!Lattice LatSt, !EqDecision Op, !Countable Op, !CrdtDenot Op LatSt}.

  Class StateCrdtModel := {
    (* The lub operation must be coherent with respect to denotations.
       We can assume that s1 and s2 are dep_closed because that is an invariant
       that is always preserved by state-based CRDTs. *)
    st_crdtM_lub_coh : ∀ (s1 s2 : gset (Event Op)) (st1 st2 st3 : LatSt),
      ⟦ s1 ⟧ ⇝ st1 ->
      ⟦ s2 ⟧ ⇝ st2 ->
      event_set_valid s1 ->
      event_set_valid s2 ->
      st1 ⊔_l st2 = st3 <-> ⟦ s1 ∪ s2 ⟧ ⇝ st3;

    (* The mutator sends a state, an operation, and the replica id where the
       mutation is taking place to a new state.  *)
    st_crdtM_mut: LatSt → Event Op → LatSt → Prop;

    (* All mutations are monotone, so always end up higher up in the lattice.  *)
    st_crdtM_mut_mon (st : LatSt) (e: Event Op) (st': LatSt) :
      st_crdtM_mut st e st' → st ≤_l st';

    (* Mutations are coherent with denotations. *)
    st_crdtM_mut_coh (s : gset (Event Op)) (st st' : LatSt) (ev: Event Op) :
      ⟦ s ⟧ ⇝ st ->
      event_set_valid s ->
      ev ∉ s ->
      is_maximum ev (s ∪ {[ ev ]}) ->
      st_crdtM_mut st ev st' <->
      ⟦ s ∪ {[ ev ]} ⟧ ⇝ st';

    (* The initial CRDT state. *)
    st_crdtM_init_st : LatSt;

    (* The initial state is the denotation of the empty set of operations. *)
    st_crdtM_init_st_coh : ⟦ ∅ ⟧ ⇝ st_crdtM_init_st
  }.

End ModelDef.
Arguments StateCrdtModel (Op LatSt) {_ _ _ _}.

