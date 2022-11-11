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

Section prod_crdt_model.
  Context `{!CRDT_Params}.
  Context `{!EqDecision opA} `{!Countable opA}
          `{!EqDecision opB} `{!Countable opB}.

  Context `{!StateLib_Res (prodOp opA opB)}.
  Context `{!anerisG M Σ}.
  Context `{latStA : Lattice stA} `{latStB : Lattice stB}.

  Context `{PA : !StLib_Params opA stA}.
  Context `{PB : !StLib_Params opB stB}.

  Notation prodOp := (prodOp opA opB).
  Notation prodSt := (prodSt stA stB).

  Lemma gos_lub_coh
        (s1 s2 : event_set prodOp) (st1 st2 st3 : prodSt):
    ⟦ s1 ⟧ ⇝ st1 → ⟦ s2 ⟧ ⇝ st2
    → Lst_Validity s1 → Lst_Validity s2 → Lst_Validity (s1 ∪ s2)
    → st1 ⊔_l st2 = st3 → ⟦ s1 ∪ s2 ⟧ ⇝ st3.
  Proof.
    intros Hd1 Hd2 Hs1 Hs2 Hsu Hlub.
    destruct PA as [pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8].
    destruct PB as [pb1 pb2 pb3 pb4 pb5 pb6 pb7 pb8].
    destruct Hd1 as (Hd11 & Hd12).
    destruct Hd2 as (Hd21 & Hd22).
    rewrite /=/prod_denot. simplify_eq /=.
    clear pa1 pa4 pa5 pa6 pa7 pa8.
    clear pb1 pb4 pb5 pb6 pb7 pb8.
    destruct st1 as (st11, st12).
    destruct st2 as (st21, st22).
    simplify_eq /=.
    rewrite! gset_map_union.
    split.
    - eapply lst_validity_valid_event_map in Hs1, Hs2, Hsu.
      destruct pa3 as [pam1 pam2 pam3 pam4 pam5 pam6].
      clear pam2 pam3 pam4 pam5 pam6.
      apply (pam1
               (gset_map (event_map fst) s1)
               (gset_map (event_map fst) s2)
            st11 st21); [done|done|done|done| |done ].
      by rewrite -gset_map_union.
    - eapply lst_validity_valid_event_map in Hs1, Hs2, Hsu.
      destruct pb3 as [pbm1 pbm2 pbm3 pbm4 pbm5 pbm6].
      clear pbm2 pbm3 pbm4 pbm5 pbm6.
      apply (pbm1
               (gset_map (event_map snd) s1)
               (gset_map (event_map snd) s2)
            st12 st22); [done|done|done|done| |done ].
      by rewrite -gset_map_union.
  Qed.

End prod_crdt_model.

 (* Global Program Instance prod_crdt_model :  *)
 (*   (StateCrdtModel (prodOp opA opB) (prodSt stA stB)). := *)
 (*    { st_crdtM_lub_coh     := gos_lub_coh; *)
 (*      st_crdtM_mut         := gos_mutator; *)
 (*      st_crdtM_mut_mon     := gos_mut_mon; *)
 (*      st_crdtM_mut_coh     := gos_mut_coh; *)
 (*      st_crdtM_init_st     := gos_st_init; *)
 (*      st_crdtM_init_st_coh := gos_init_coh; }. *)

 (*  Global Program Instance prod_crdt_params :  *)
 (*   StLib_Params (prodOp opA opB) (prodSt stA stB) := *)
 (*    { *)
 (*      StLib_StSerialization :=  *)
 (*      prod_serialization  *)
 (*        PA.(StLib_StSerialization) PB.(StLib_StSerialization); *)
 (*      StLib_Denot := prod_denot_instance PA.(StLib_Denot) PB.(StLib_Denot); }. *)
 (*      StLib_Model           := gos_model; *)
 (*      StLib_Op_Coh          := gos_op_coh; *)
 (*      StLib_Op_Coh_Inj      := gos_op_coh_inj; *)
 (*      StLib_St_Coh          := gos_st_coh; *)
 (*      StLib_St_Coh_Inj      := gos_st_coh_inj; *)
 (*      StLib_StCoh_Ser       := gos_st_coh_serializable *)
 (* }. *)

  (* Definition gos_mutator (st: @gos_st gos_op _ _) (ev: Event gos_op) (st': gos_st) : Prop := *)
  (*   st' = st ∪ {[ev.(EV_Op)]}. *)

  (* Lemma gos_mut_mon (st : gos_st) (e: Event gos_op) (st': gos_st) : *)
  (*   gos_mutator st e st' → st ≤_l st'. *)
  (* Proof. set_solver. Qed. *)
