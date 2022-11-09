From Coq Require Import ssreflect Vector.
From stdpp Require Import base gmap vector.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import gset_map.
From aneris.prelude Require Import misc strings.
From aneris.aneris_lang.lib Require Import network_util_proof.
From aneris.aneris_lang.lib Require Import list_proof set_proof inject.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import aneris_lifting proofmode.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_code vector_clock_proof.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_denot crdt_resources.
From aneris.examples.crdt.statelib.user_model
     Require Import semi_join_lattices model params.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.STS Require Import lst.
From aneris.examples.crdt.statelib.proof
     Require Import events spec.
From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.examples.crdt.statelib.examples.prod_comb
     Require Import prod_comb_code.

(* TODO: Move to semi-lattices. *)
Section prodLattice.
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

End prodLattice.

Section prod_crdt_denot.
  Context `{!CRDT_Params} `{!Log_Time}
          `{!EqDecision opA} `{!Countable opA}
          `{!EqDecision opB} `{!Countable opB}
          `(crdt_denotA : !CrdtDenot opA stA)
          `(crdt_denotB : !CrdtDenot opB stB)
          `{latStA : Lattice stA}
          `{latStB : Lattice stB}.

  Definition prodOp : Type := opA * opB.
  Definition prodSt : Type := stA * stB.

  Definition prod_denot (s : event_set prodOp) (st : prodSt) : Prop :=
    crdt_denot (gset_map (event_map fst) s) st.1 ∧
    crdt_denot (gset_map (event_map snd) s) st.2.

  Global Instance prod_denot_fun : Rel2__Fun prod_denot.
  Proof.
    constructor; intros ? [] [] [] [];
      simpl in *; f_equal; eapply @rel2_fun; eauto; apply _.
  Qed.

  Global Instance prod_denot_instance : CrdtDenot prodOp prodSt := {
    crdt_denot := prod_denot;
    crdt_denot_fun := prod_denot_fun;
  }.

  Global Instance prod_st_le_lat : Lattice prodSt :=
    prod_lattice latStA latStB.

 End prod_crdt_denot.

Global Arguments prodOp _ _ : clear implicits.
Global Arguments prodSt _ _ : clear implicits.
