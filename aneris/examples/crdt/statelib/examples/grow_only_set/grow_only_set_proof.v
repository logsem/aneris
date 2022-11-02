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


Section gos_denot.
  Context `{!vl : Type}.
  Context `{!CRDT_Params} `{!Log_Time}.
  Context `{!EqDecision vl} `{!Countable vl}.

  (** Definition of operations and states. *)
  Definition gos_op : Type := vl.
  Definition gos_st : Type := gset vl.

  (** Definition of the denotation. *)
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

  Global Instance gset_subset_po : PartialOrder  (⊆@{gset vl}).
  Proof. repeat split; repeat intro; multiset_solver. Qed.

  Lemma gset_union_lub_spec :
    ∀ e1 e2 : gos_st, e1 ⊆ e1 ∪ e2 ∧
                        e2 ⊆ e1 ∪ e2 ∧
                        (∀ e : gos_st, e1 ⊆ e → e2 ⊆ e → e1 ∪ e2 ⊆ e).
  Proof. repeat split; repeat intro; multiset_solver. Qed.


  (** Instantiation of the Join-Semi-Lattice. *)
  Global Instance gos_st_le_lat : Lattice gos_st :=
    { lat_le := (⊆);
      lat_po := gset_subset_po;
      lat_lub := (∪);
      lat_lub_spec := gset_union_lub_spec }.

End gos_denot.

Section gos_model.
  Context `{!CRDT_Params}.
  Context `{!EqDecision vl} `{!Countable vl}.
  Context `{!EventSetValidity vl}.


  Definition gos_mutator
             (st: @gos_st gos_op _ _) (ev: Event gos_op) (st': gos_st) : Prop :=
    st' = st ∪ {[ev.(EV_Op)]}.

  Lemma gos_mut_mon (st : gos_st) (e: Event gos_op) (st': gos_st) :
    gos_mutator st e st' → st ≤_l st'.
  Proof. set_solver. Qed.

  Lemma gos_mut_coh
        (s : event_set gos_op) (st st' : gos_st) (ev: Event gos_op) :
    ⟦ s ⟧ ⇝ st ->
    event_set_valid s ->
    ev ∉ s ->
    is_maximum ev (s ∪ {[ ev ]}) ->
    gos_mutator st ev st' -> ⟦ s ∪ {[ ev ]} ⟧ ⇝ st'.
  Proof.
    rewrite /=/gos_denot_prop /gos_mutator.
    intros ???? ->. by set_solver.
  Qed.

  Lemma gos_lub_coh
        (s1 s2 : event_set gos_op) (st1 st2 st3 : (@gos_st gos_op _ _)):
    ⟦ s1 ⟧ ⇝ st1 → ⟦ s2 ⟧ ⇝ st2
    → event_set_valid s1 → event_set_valid s2 → event_set_valid (s1 ∪ s2)
    → st1 ⊔_l st2 = st3 → ⟦ s1 ∪ s2 ⟧ ⇝ st3.
  Proof.
    rewrite /=/gos_denot_prop.
    intros <- <- Hval1 Hval2 Hval <-.
    by rewrite gset_map_union.
  Qed.

  Definition gos_st_init : (@gos_st gos_op _ _) := ∅.

  Lemma gos_init_coh : ⟦ ∅ ⟧ ⇝ gos_st_init.
  Proof. by set_solver. Qed.

  Global Instance gos_model : (StateCrdtModel gos_op gos_st) :=
    { st_crdtM_lub_coh     := gos_lub_coh;
      st_crdtM_mut         := gos_mutator;
      st_crdtM_mut_mon     := gos_mut_mon;
      st_crdtM_mut_coh     := gos_mut_coh;
      st_crdtM_init_st     := gos_st_init;
      st_crdtM_init_st_coh := gos_init_coh; }.

End gos_model.

Section gos_params.

  Context `{!CRDT_Params}.
  Context `{!EqDecision vl} `{!Countable vl}.
  Context `{!EventSetValidity vl}.

  (* Lemma gos_st_coh_is_vc (st: gos_st): *)
  (*   is_vc (gos_st_inject st) st. *)
  (* Proof. *)
  (*   rewrite/gos_st_inject/is_vc. *)
  (*   apply is_list_inject. reflexivity. *)
  (* Qed. *)

  (* Lemma gos_st_coh_serializable *)
  (*       (st : gos_st) (v : val): *)
  (*   gos_st_coh st v → Serializable gos_ser v. *)
  (* Proof. *)
  (*   intros->. *)
  (*   exists st. exact (gos_st_coh_is_vc st). *)
  (* Qed. *)


  (* Global Instance gos_params : (StLib_Params gos_op gos_st) := *)
  (*   { *)
  (*     StLib_StSerialization := gos_ser; *)
  (*     StLib_Denot           := gos_denot; *)
  (*     StLib_Model           := gos_model; *)
  (*     StLib_Op_Coh          := gos_op_coh; *)
  (*     StLib_Op_Coh_Inj      := gos_op_coh_inj; *)
  (*     StLib_St_Coh          := gos_st_coh; *)
  (*     StLib_St_Coh_Inj      := gos_st_coh_inj; *)
  (*     StLib_StCoh_Ser       := gos_st_coh_serializable }. *)

End gos_params.
