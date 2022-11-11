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

Section Set_Lattice.
  Context `{!EqDecision E, !Countable E}.

  Global Instance gset_subset_po : PartialOrder  (⊆@{gset E}).
  Proof. repeat split; repeat intro; multiset_solver. Qed.

  Lemma gset_union_lub_spec :
    ∀ e1 e2 : gset E, e1 ⊆ e1 ∪ e2 ∧
                        e2 ⊆ e1 ∪ e2 ∧
                        (∀ e : gset E, e1 ⊆ e → e2 ⊆ e → e1 ∪ e2 ⊆ e).
  Proof. repeat split; repeat intro; multiset_solver. Qed.


  (** Instantiation of the Join-Semi-Lattice. *)
  Global Instance gos_st_le_lat : Lattice (gset E) :=
    { lat_le := (⊆);
      lat_po := gset_subset_po;
      lat_lub := (∪);
      lat_lub_spec := gset_union_lub_spec }.

End Set_Lattice.

Section Prod_Lattice.
  Definition prod_lat_le {A B: Type} (latA : Lattice A) (latB : Lattice B)
    : relation (A * B) :=
    fun (p1 : A * B) (p2 : A * B) =>
      latA.(lat_le) p1.1 p2.1 ∧ latB.(lat_le) p1.2 p2.2.

  Global Instance prod_lat_le_po {A B: Type}
         (latA : Lattice A) (latB : Lattice B)
    : PartialOrder (prod_lat_le latA latB).
  Proof.
    destruct latA as [leA poA lubA specA].
    destruct latB as [leB poB lubB specB].
    destruct poA as ((HpoA11 & HpoA12) & HpoA2).
    destruct poB as ((HpoB11 & HpoB12) & HpoB2).
    repeat (split; rewrite! /prod_lat_le);
      repeat (intros (x1,x2) (y1,y2) Hx Hy); try naive_solver.
    by f_equal; naive_solver.
  Qed.

  Definition prod_lat_lub {A B: Type} (latA : Lattice A) (latB : Lattice B)
    : (A * B) → (A * B) → (A * B) :=
    fun (p1 : A * B) (p2 : A * B) =>
      ((latA.(lat_lub) p1.1 p2.1), (latB.(lat_lub) p1.2 p2.2)).

  Lemma prod_lat_lub_spec {A B: Type}
        (latA : Lattice A) (latB : Lattice B) :
    ∀ e1 e2,
    (prod_lat_le latA latB)
      e1 ((prod_lat_lub latA latB) e1 e2)
      ∧ (prod_lat_le latA latB)
          e2 ((prod_lat_lub latA latB) e1 e2)
      ∧ ∀ e, (prod_lat_le latA latB) e1 e →
              (prod_lat_le latA latB) e2 e →
              (prod_lat_le latA latB) ((prod_lat_lub latA latB) e1 e2) e.
  Proof.
    destruct latA as [leA poA lubA specA].
    destruct latB as [leB poB lubB specB].
    repeat (split; rewrite /prod_lat_le); repeat intro; naive_solver.
  Qed.


  (** Instantiation of the Join-Semi-Lattice. *)
  Global Instance prod_lattice {A B: Type}
         (latA : Lattice A) (latB : Lattice B): Lattice (A * B) :=
    { lat_le := prod_lat_le latA latB;
      lat_po := prod_lat_le_po latA latB;
      lat_lub := prod_lat_lub latA latB;
      lat_lub_spec := prod_lat_lub_spec latA latB }.

End Prod_Lattice.


From Coq Require Import ssreflect Vector.
From stdpp Require Import base gmap vector.

From Coq Require Import ssreflect Vector.
From stdpp Require Import base gmap vector.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang.lib Require Import list_proof inject.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import aneris_lifting proofmode.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_denot crdt_resources.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.STS Require Import lst.
From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_code vector_clock_proof.

(** Definition of the ordering on the states *)
Section VectNat_Lattice.
  Context (n : nat).

  Definition vectn : Type := vec nat n.

  Definition vectn_le (st st': vectn) : Prop :=
    Forall2 le st st'.

  Global Instance vectn_le_trans : Transitive vectn_le.
  Proof.
    intros st st' st'' H1 H2.
    rewrite /vectn_le Forall2_vlookup.
    intros i.
    rewrite /vectn_le Forall2_vlookup in H1. specialize H1 with i.
    rewrite /vectn_le Forall2_vlookup in H2. specialize H2 with i.
    lia.
  Qed.
  Global Instance vectn_le_refl : Reflexive vectn_le.
  Proof.
    intros v.
    by rewrite /vectn_le Forall2_vlookup.
  Qed.
  Global Instance vectn_le_anti_symm : AntiSymm eq vectn_le.
  Proof.
    intros st st' H1 H2.
    apply vec_eq. intros i.
    rewrite /vectn_le Forall2_vlookup in H1. specialize H1 with i.
    rewrite /vectn_le Forall2_vlookup in H2. specialize H2 with i.
    lia.
  Qed.

  Global Instance vectn_le_PreOrder : PreOrder vectn_le :=
    { PreOrder_Reflexive  := vectn_le_refl;
      PreOrder_Transitive := vectn_le_trans; }.

  Global Instance vectn_le_po : PartialOrder vectn_le :=
    { partial_order_pre       := vectn_le_PreOrder;
      partial_order_anti_symm := vectn_le_anti_symm; }.

  Definition vectn_lub : vectn -> vectn -> vectn :=
    map2 Nat.max.

  Lemma vectn_lub_prop (st st' : vectn) :
    vectn_le st (vectn_lub st st')
    ∧ vectn_le st' (vectn_lub st st')
    ∧ (∀ e : vectn,
      vectn_le st e → vectn_le st' e → vectn_le (vectn_lub st st') e).
  Proof.
    repeat split.
    - rewrite/vectn_le Forall2_vlookup/vectn_lub. intros i.
      rewrite vlookup_zip_with. lia.
    - rewrite/vectn_le Forall2_vlookup/vectn_lub. intros i.
      rewrite vlookup_zip_with. lia.
    - intros st'' H1 H2.
      rewrite/vectn_le Forall2_vlookup/vectn_lub. intros i.
      rewrite vlookup_zip_with.
      rewrite/vectn_le Forall2_vlookup/vectn_lub in H1.
        specialize H1 with i.
      rewrite/vectn_le Forall2_vlookup/vectn_lub in H2.
        specialize H2 with i.
      by apply Nat.max_lub.
  Qed.

  (** Instantiation of the Join-Semi-Lattice *)
  Global Instance vectn_le_lat : Lattice vectn:=
    { lat_le := vectn_le;
      lat_po := vectn_le_po;
      lat_lub := vectn_lub;
      lat_lub_spec := vectn_lub_prop; }.

  End VectNat_Lattice.
