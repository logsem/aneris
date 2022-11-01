From Coq Require Import ssreflect Vector.
From stdpp Require Import base gmap vector.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import gset_map.
From aneris.aneris_lang.lib Require Import list_proof inject.
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
From aneris.examples.crdt.statelib.examples.grow_only_set Require Import grow_only_set_code.



Section gosCrdt.

  Context `{!CRDT_Params}.
  Context `{!Log_Time} `{!EqDecision vl} `{!Countable vl}.

  (** Definition of operations and states *)
  Definition gos_op : Type := vl.
  Definition gos_st : Type := gset vl.

  (** Definition of the Denotation *)
  Definition gos_denot_prop (s: event_set gos_op) (st: gos_st) :=
    gset_map (fun (ev: Event gos_op) => ev.(EV_Op)) s = st.

  Global Instance gos_denot_fun : Rel2__Fun gos_denot_prop.
  Proof.
    constructor; unfold gos_denot_prop; intros s st st' Hst Hst'.
    by rewrite -Hst -Hst'.
  Qed.

  Global Instance gos_denot : CrdtDenot gos_op gos_st :=
    { crdt_denot     := gos_denot_prop;
      crdt_denot_fun := gos_denot_fun; }.



  (** Instantiation of the Join-Semi-Lattice *)
  (* Global Instance gctr_st_le_lat : Lattice gos_st := *)
  (*   { lat_le := gset_subseteq_dec; *)
  (*     lat_po := ???; *)
  (*     lat_lub := gset_union; *)
  (*     lat_lub_spec := ???; }. *)


End gosCrdt.
