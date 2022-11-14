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
  Context `{!Inject opA val} `{!Inject opB val}.
  Context `{!Inject stA val} `{!Inject stB val}.

  Context `{PA : !StLib_Params opA stA}.
  Context `{PB : !StLib_Params opB stB}.

  Notation prodOp := (prodOp opA opB).
  Notation prodSt := (prodSt stA stB).

  Lemma prod_lub_coh
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

  Definition prod_mutator (st : prodSt) (ev: Event prodOp) (st': prodSt) : Prop :=
    PA.(StLib_Model).(st_crdtM_mut) st.1 (event_map fst ev) st'.1 ∧
    PB.(StLib_Model).(st_crdtM_mut) st.2 (event_map snd ev) st'.2.

  Lemma prod_mut_mon (st : prodSt) (e: Event prodOp) (st': prodSt) :
    prod_mutator st e st' → st ≤_l st'.
  Proof.
    intros (Hp1 & HP2).
    split;
      [ by eapply PA.(StLib_Model).(st_crdtM_mut_mon)
      | by eapply PB.(StLib_Model).(st_crdtM_mut_mon)].
  Qed.

  Lemma prod_mut_coh (s : event_set prodOp) (st st' : prodSt) (ev: Event prodOp) :
    ⟦ s ⟧ ⇝ st ->
    Lst_Validity s ->
    ev ∉ s ->
    is_maximum ev (s ∪ {[ ev ]}) ->
    prod_mutator st ev st' -> ⟦ s ∪ {[ ev ]} ⟧ ⇝ st'.
  Proof.
    rewrite /=/prod_denot /prod_mutator.
    intros (Hd1 & Hd2) Hv Hev Hm (Hm1 & Hm2).
    rewrite! gset_map_union ! gset_map_singleton.
    assert (Lst_Validity (gset_map (event_map fst) s) ∧
              Lst_Validity (gset_map (event_map snd) s)).
    { split; by apply lst_validity_valid_event_map. }
    assert (event_map fst ev ∉ gset_map (event_map fst) s ∧
              event_map snd ev ∉ gset_map (event_map snd) s).
    { split.
      - intro Habs.
        apply Hev.
        apply gset_map_correct2 in Habs.
        destruct Habs as (a & Ha & Hin).
        inversion Ha.
        destruct Hm as (HinM & Ht).
        assert (a = ev ∨ a ≠ ev) as [->| Hneq] by naive_solver; first done.
        epose proof (Ht a _ Hneq); set_solver. Unshelve. by set_solver.
      - intro Habs.
        apply Hev.
        apply gset_map_correct2 in Habs.
        destruct Habs as (a & Ha & Hin).
        inversion Ha.
        destruct Hm as (HinM & Ht).
        assert (a = ev ∨ a ≠ ev) as [->| Hneq] by naive_solver; first done.
        epose proof (Ht a _ Hneq); set_solver. Unshelve. by set_solver. }
    assert ( is_maximum (event_map fst ev)
                        (gset_map (event_map fst) s ∪ {[event_map fst ev]}) ∧
               is_maximum (event_map snd ev)
                          (gset_map (event_map snd) s ∪ {[event_map snd ev]})).
    { destruct Hm as (HinM & Ht).
      split.
      - split; first set_solver.
        intros a Ha Hneqt.
        assert (a ∈ gset_map (event_map fst) s) as Hain by set_solver.
        apply gset_map_correct2 in Hain as (a0  & Ha0 & Ha0in).
        assert (a0 ≠ ev) as Hneq0.
        { intro.
          apply Hneqt.
          set_solver. }
        epose proof (Ht a0 _ Hneq0); set_solver. Unshelve. set_solver.
      -  split; first set_solver.
         intros a Ha Hneqt.
         assert (a ∈ gset_map (event_map snd) s) as Hain by set_solver.
         apply gset_map_correct2 in Hain as (a0  & Ha0 & Ha0in).
         assert (a0 ≠ ev) as Hneq0.
         { intro.
           apply Hneqt.
           set_solver. }
         epose proof (Ht a0 _ Hneq0); set_solver. Unshelve. set_solver.
    }
    split.
    - eapply (PA.(StLib_Model).(st_crdtM_mut_coh) _ st.1 st'.1 ); try naive_solver.
    - eapply (PB.(StLib_Model).(st_crdtM_mut_coh) _ st.2 st'.2 ); try naive_solver.
  Qed.


  Definition prodSt_init : prodSt :=
    (PA.(StLib_Model).(st_crdtM_init_st), PB.(StLib_Model).(st_crdtM_init_st)).

  Lemma prodSt_init_coh : ⟦ ∅ ⟧ ⇝ prodSt_init.
  Proof.
    split.
    - apply (PA.(StLib_Model).(st_crdtM_init_st_coh)).
    - apply (PB.(StLib_Model).(st_crdtM_init_st_coh)).
  Qed.

  Global Instance prod_crdt_model :
    (StateCrdtModel prodOp prodSt) :=
    { st_crdtM_lub_coh     := prod_lub_coh;
      st_crdtM_mut         := prod_mutator;
      st_crdtM_mut_mon     := prod_mut_mon;
      st_crdtM_mut_coh     := prod_mut_coh;
      st_crdtM_init_st     := prodSt_init;
      st_crdtM_init_st_coh := prodSt_init_coh; }.

  Definition prodOp_coh (op: prodOp) (v: val) : Prop :=
    v = $op ∧ s_valid_val (prod_serialization PA.(StLib_StSerialization) PB.(StLib_StSerialization)) $ v.

  Lemma prodOp_coh_inj (o o': prodOp) (v: val) :
    prodOp_coh o v -> prodOp_coh o' v -> o = o'.
  Proof.
    intros (Hv & _) (Hv' & _).
    rewrite/prodOp_coh in Hv. rewrite/prodOp_coh in Hv'.
    rewrite Hv in Hv'.
    by apply (@inject_inj _ val) in Hv'.
  Qed.

  Definition prodSt_coh (st: prodSt) (v: val) : Prop :=
  ∃ (v1 v2 : val), v = $st ∧ (v1, v2)%V = v ∧
     PA.(StLib_St_Coh) st.1 v1 ∧
     PB.(StLib_St_Coh) st.2 v2.

  Lemma prodSt_coh_inj (st st': prodSt) (v: val) :
    prodSt_coh st v -> prodSt_coh st' v -> st = st'.
  Proof.
    intros (v11 & v12 & Heq11 & Heq12 & (Hp11 & Hp12))
           (v21 & v22 & Heq21 & Heq22 & (Hp21 & Hp22)).
    rewrite -Heq12 in Heq22.
    inversion Heq22. subst.
    destruct st, st'.
    f_equal /=.
    - by eapply PA.(StLib_St_Coh_Inj).
    - by eapply PB.(StLib_St_Coh_Inj).
  Qed.

  Lemma prodSt_coh_serializable :
    (∀ (st : prodSt) (v : val),
       prodSt_coh st v
       → Serializable
           (prod_serialization PA.(StLib_StSerialization) PB.(StLib_StSerialization))
           v).
  Proof.
    intros st v Hcoh.
    simpl.
    rewrite /prodSt_coh in Hcoh.
    destruct Hcoh as (v1 & v2 & Heq1 & Heq2 & Hcoh1 & Hcoh2).
    exists v1, v2.
    split; first done.
    split.
    - apply (PA.(StLib_StCoh_Ser) st.1 v1 Hcoh1).
    - apply (PB.(StLib_StCoh_Ser) st.2 v2 Hcoh2).
  Qed.



  Global Program Instance prod_crdt_params :
   StLib_Params prodOp prodSt :=
    {
      StLib_StSerialization :=
      prod_serialization
        PA.(StLib_StSerialization) PB.(StLib_StSerialization);
      StLib_Denot := prod_denot_instance PA.(StLib_Denot) PB.(StLib_Denot);
      StLib_Model           := prod_crdt_model;
      StLib_Op_Coh_Inj      := prodOp_coh_inj;
      StLib_St_Coh          := prodSt_coh;
      StLib_St_Coh_Inj      := prodSt_coh_inj;
      StLib_StCoh_Ser       := prodSt_coh_serializable
    }.

End prod_crdt_model.
