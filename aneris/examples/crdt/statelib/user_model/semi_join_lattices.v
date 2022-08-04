From aneris.aneris_lang Require Import lang.

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

