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
  Context (opA : Type) (stA : Type).
  Context (opB : Type) (stB : Type).
  Context `{!Log_Time}.
  Context `{!EqDecision opA} `{!Countable opA}.
  Context `{!EqDecision opB} `{!Countable opB}.
  Context `(crdt_denotA : !CrdtDenot opA stA).
  Context `(crdt_denotB : !CrdtDenot opB stB).
  Context `{latStA : Lattice stA} `{latStB : Lattice stB}.
  Context `{!CRDT_Params}.

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

(* Global Arguments prodOp _ _ : clear implicits. *)
(* Global Arguments prodSt _ _ : clear implicits. *)

Section prod_crdt_model.

  Context (opA : Type) (stA : Type).
  Context (opB : Type) (stB : Type).
  Context `{!EqDecision opA} `{!Countable opA}.
  Context `{!EqDecision opB} `{!Countable opB}.
  Context `{!Inject opA val} `{!Inject opB val}.
  Context `{!Inject stA val} `{!Inject stB val}.
  Context `{latStA : Lattice stA} `{latStB : Lattice stB}.
  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.
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
    - eapply (lst_validity_valid_event_map _ fst) in Hs1, Hs2, Hsu.
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
      - by apply event_map_max_not_in.
      - by apply event_map_max_not_in. }
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
    ∃ (v1 v2 : val), (v1, v2)%V = v ∧
    PA.(StLib_Op_Coh) op.1 v1 ∧
    PB.(StLib_Op_Coh) op.2 v2 ∧
    s_valid_val (prod_serialization PA.(StLib_StSerialization) PB.(StLib_StSerialization)) $ v.

  Lemma prodOp_coh_inj (o o': prodOp) (v: val) :
    prodOp_coh o v -> prodOp_coh o' v -> o = o'.
  Proof.
     intros (v11 & v12 &  Heq12 & (Hp11 & Hp12 & _))
           (v21 & v22 &  Heq22 & (Hp21 & Hp22 & _)).
     rewrite/prodOp_coh in Hp11.
     rewrite/prodOp_coh in Hp22.
     rewrite -Heq12 in Heq22.
     inversion Heq22. subst.
     destruct o, o'.
     f_equal /=.
    - by eapply PA.(StLib_Op_Coh_Inj).
    - by eapply PB.(StLib_Op_Coh_Inj).
  Qed.

  Definition prodSt_coh (st: prodSt) (v: val) : Prop :=
  ∃ (v1 v2 : val), (v1, v2)%V = v ∧
     PA.(StLib_St_Coh) st.1 v1 ∧
     PB.(StLib_St_Coh) st.2 v2.

  Lemma prodSt_coh_inj (st st': prodSt) (v: val) :
    prodSt_coh st v -> prodSt_coh st' v -> st = st'.
  Proof.
    intros (v11 & v12 &  Heq12 & (Hp11 & Hp12))
           (v21 & v22 &  Heq22 & (Hp21 & Hp22)).
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
           (prod_serialization PA.(StLib_StSerialization) PB.(StLib_StSerialization)) v).
  Proof.
    intros st v Hcoh.
    simpl.
    rewrite /prodSt_coh in Hcoh.
    destruct Hcoh as (v1 & v2 & Heq2 & Hcoh1 & Hcoh2).
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
      StLib_Denot := prod_denot_instance opA stA opB stB PA.(StLib_Denot) PB.(StLib_Denot);
      StLib_Model           := prod_crdt_model;
      StLib_Op_Coh_Inj      := prodOp_coh_inj;
      StLib_St_Coh          := prodSt_coh;
      StLib_St_Coh_Inj      := prodSt_coh_inj;
      StLib_StCoh_Ser       := prodSt_coh_serializable
    }.

End prod_crdt_model.

Section prod_proof.
  Context (opA : Type) (stA : Type).
  Context (opB : Type) (stB : Type).
  Context `{!EqDecision opA} `{!Countable opA}
          `{!EqDecision opB} `{!Countable opB}.
  Context `{!Inject opA val} `{!Inject opB val}.
  Context `{!Inject stA val} `{!Inject stB val}.
  Context `{latStA : Lattice stA} `{latStB : Lattice stB}.
  Context `{!anerisG M Σ}.
  Context `{!CRDT_Params}.
  Context `{PA : !StLib_Params opA stA}.
  Context `{PB : !StLib_Params opB stB}.

  Global Instance prod_params : StLib_Params (prodOp opA opB) (prodSt stA stB).
  Proof. exact (prod_crdt_params opA stA opB stB). Defined.

  Lemma prod_init_st_fn_spec initA initB :
    @init_st_fn_spec _ _ _ _ _ _ stA _ _ PA initA -∗
    @init_st_fn_spec _ _ _ _ _ _ stB _ _ PB initB -∗
    @init_st_fn_spec _ _ _ _ _ _ (prodSt stA stB) _ _ prod_params (λ: <>, init_st initA initB #()).
  Proof.
    iIntros "#HA #HB" (addr).
    iIntros "!#" (Φ) "_ HΦ".
    do 2 wp_lam.
    wp_pures.
    wp_apply "HB"; first done.
    iIntros (vB HvB).
    wp_apply "HA"; first done.
    iIntros (vA HvA).
    wp_pures.
    iApply "HΦ".
    iPureIntro. eexists _, _; eauto.
  Qed.

  Lemma prod_mutator_st_spec mut_fnA mut_fnB :
    @mutator_spec _ _ _ _ _ _ stA _ _ PA mut_fnA -∗
    @mutator_spec _ _ _ _ _ _ stB _ _ PB mut_fnB -∗
    @mutator_spec _ _ _ _ _ _ _ _ _ prod_params
                  (λ: "i" "gs" "op", mutator mut_fnA mut_fnB "i" "gs" "op").
  Proof.
    iIntros "#HA #HB" (addr id st_v op_v s ev op_log st_log)
                 "!> %φ ((%v1 & %v2 & <- & %Hv1 & %Hv2 & %Hvv) &
                 (%stv1 & %stv2 & <- & %Hst_coh & %Hst_coh') & %Hden &
                    %Hnin & <- & <- & %Hmax & %Hext & %Hsoc) Hφ".
    destruct ev as [[op1 op2] orig vc].
    wp_lam. wp_pures.
    wp_lam. wp_pures.
    wp_apply ("HB" $! _ _ stv2 v2
                    (gset_map (event_map snd) s)
                    (event_map snd {| EV_Op := (op1, op2); EV_Orig := orig; EV_Time := vc |})
                    op2 st_log.2).
    iPureIntro.
    inversion Hden as [Hden1 Hden2].
    split_and!; try eauto with set_solver.
    - by apply event_map_max_not_in.
    - rewrite -gset_map_singleton -gset_map_union.
      by apply event_map_is_maximum.
    - rewrite -gset_map_singleton -gset_map_union.
      by apply events_ext_map.
    - rewrite -gset_map_singleton -gset_map_union.
      by apply event_map_is_same_orig_comparable.
    - iIntros (v2') "(%lg2 & %Hstc2 & %Hϕ2)".
      wp_apply ("HA" $! _ _ stv1 v1
                     (gset_map (event_map fst) s)
                     (event_map fst {| EV_Op := (op1, op2); EV_Orig := orig; EV_Time := vc |})
                     op1 st_log.1).
      iPureIntro.
      inversion Hden as [Hden1 Hden2].
      split_and!; try eauto with set_solver.
      -- by apply event_map_max_not_in.
      -- rewrite -gset_map_singleton -gset_map_union.
         by apply event_map_is_maximum.
      -- rewrite -gset_map_singleton -gset_map_union.
         by apply events_ext_map.
      -- rewrite -gset_map_singleton -gset_map_union.
         by apply event_map_is_same_orig_comparable.
      -- iIntros (v1') "(%lg1 & %Hstc1 & %Hϕ1)".
         wp_pures.
         iApply "Hφ".
         iPureIntro.
         exists (lg1, lg2).
         rewrite /StLib_St_Coh /= /prodSt_coh /prod_mutator /=.
         split_and!; try eauto.
  Qed.

  Definition prod_crdt' : val :=
    (λ: "cA" "cB" <>,
        let: "cAp" := "cA" #() in
        let: "cBp" := "cB" #() in
        let: "init_fnA" := Fst (Fst "cAp") in
        let: "mut_fnA" := Snd (Fst "cAp") in
        let: "merge_fnA" := Snd "cAp" in
        let: "init_fnB" := Fst (Fst "cBp") in
        let: "mut_fnB" := Snd (Fst "cBp") in
        let: "merge_fnB" := Snd "cBp" in
        let: "init_fn" := (λ: <>, init_st "init_fnA" "init_fnB" #()) in
        let: "mut_fn" := (λ: "i" "gs" "op", mutator "mut_fnA" "mut_fnB" "i" "gs" "op") in
        let: "merge_fn" := (λ: "st1" "st2", merge "merge_fnA" "merge_fnB" "st1" "st2") in
        ("init_fn", "mut_fn", "merge_fn"))%V.

  Definition prod_init' (stA_ser : val) (stA_deser : val) (stB_ser : val)
             (stB_deser : val) : val :=
    λ: "cA" "cB" "addrs" "rid",
      let: "initRes" := statelib_init (prod_ser stA_ser stB_ser)
                                      (prod_deser stA_deser stB_deser) "addrs" "rid"
                                      (λ: <>, prod_crdt' "cA" "cB" #()) in
      let: "get_state" := Fst "initRes" in
      let: "update" := Snd "initRes" in
      ("get_state", "update").


  Lemma prod_merge_st_spec merge_fnA merge_fnB :
    @merge_spec _ _ _ _ _ _ stA _ _ PA merge_fnA -∗
    @merge_spec _ _ _ _ _ _ stB _ _ PB merge_fnB -∗
    @merge_spec _ _ _ _ _ _ _ _ _ prod_params
                  (λ: "st1" "st2", merge merge_fnA merge_fnB "st1" "st2").
  Proof.
    iIntros  "#HA #HB" (sa v v' s s' st st')
            "!> %φ (%Hcoh_st & %Hcoh_st' & %Hden & %Hden' &
                    %Hext & %Hsoc & %Hext' & %Hsoc') Hφ".
    destruct Hcoh_st as (v11 & v12 & <- & Hv11 & Hv12).
    destruct Hcoh_st' as (v21 & v22 & <- & Hv21 & Hv22).
    wp_lam. wp_let.
    wp_lam. wp_pures.
    inversion Hden as [Hden1 Hden2].
    inversion Hden' as [Hden'1 Hden'2].
    wp_apply ("HA" $! _ v11 v21
                    (gset_map (event_map fst) s)
                    (gset_map (event_map fst) s')
                    st.1
                    st'.1).
    - iPureIntro.
       split_and!; try eauto with set_solver.
       -- by apply events_ext_map.
       -- by apply event_map_is_same_orig_comparable.
       -- by apply events_ext_map.
       -- by apply event_map_is_same_orig_comparable.
    - iIntros (v1')  "(%lg1 & %Hstc1 & %Hϕ1)".
      wp_pures.
      wp_apply ("HB" $! _ v12 v22
                    (gset_map (event_map snd) s)
                    (gset_map (event_map snd) s')
                    st.2
                    st'.2).
      -- iPureIntro.
       split_and!; try eauto with set_solver.
         --- by apply events_ext_map.
         --- by apply event_map_is_same_orig_comparable.
         --- by apply events_ext_map.
         --- by apply event_map_is_same_orig_comparable.
      -- iIntros (v2')  "(%lg2 & %Hstc2 & %Hϕ2)".
         wp_pures.
         iApply "Hφ".
         iPureIntro.
         exists (lg1, lg2).
         rewrite /StLib_St_Coh /= /prodSt_coh /prod_lat_lub /=.
         split_and!; try eauto.
         by f_equal.
  Qed.

  Lemma prod_crdt_fun_spec cA cB :
      @crdt_fun_spec _ _ _ _ _ _ stA _ _ PA cA -∗
      @crdt_fun_spec _ _ _ _ _ _ stB _ _ PB cB -∗
      @crdt_fun_spec _ _ _ _ _ _ _ _ _ prod_params (λ: <>, prod_crdt' cA cB #()).
    Proof.
      iIntros "#HA #HB" (sa φ) "!> _ Hφ".
      wp_lam; wp_pures. wp_lam. wp_pures.
      wp_apply "HA"; first done.
      iIntros (c1) "(%c11 & %c12 & %c13 & -> & Hc11 & Hc12 & Hc13)".
      wp_pures.
      wp_apply "HB"; first done.
      iIntros (c2) "(%c21 & %c22 & %c23 & -> & Hc21 & Hc22 & Hc23)".
      wp_pures.
      iApply "Hφ".
      iExists _, _, _. iSplit; first eauto.
      iSplitL "Hc11 Hc21".
      - iApply (prod_init_st_fn_spec c11 c21 with "[$Hc11][$Hc21]") .
      - iSplitL "Hc12 Hc22".
        iApply (prod_mutator_st_spec c12 c22 with "[$Hc12][$Hc22]").
       iApply (prod_merge_st_spec c13 c23 with "[$Hc13][$Hc23]").
    Qed.

  Lemma prod_init_spec `{!StLib_Res (prodOp opA opB)} cA cB :
    @crdt_fun_spec _ _ _ _ _ _ stA _ _ PA cA -∗
    @crdt_fun_spec _ _ _ _ _ _ stB _ _ PB cB -∗
    @init_spec
      _ _ _ _ _ _ _ _ _ prod_params _
      (statelib_init
         (prod_ser
            (PA.(StLib_StSerialization).(s_serializer)).(s_ser)
            (PB.(StLib_StSerialization).(s_serializer)).(s_ser))
         (prod_deser
            (PA.(StLib_StSerialization).(s_serializer)).(s_deser)
            (PB.(StLib_StSerialization).(s_serializer)).(s_deser))) -∗
    @init_spec_for_specific_crdt
      _ _ _ _ _ _ _ _ _  prod_params _
      (λ: "addrs" "rid",
         prod_init'
          (PA.(StLib_StSerialization).(s_serializer)).(s_ser)
          (PA.(StLib_StSerialization).(s_serializer)).(s_deser)
          (PB.(StLib_StSerialization).(s_serializer)).(s_ser)
          (PB.(StLib_StSerialization).(s_serializer)).(s_deser)
          cA cB "addrs" "rid").
  Proof.
    iIntros "#HA #HB #Hinit" (repId addr addrs_val).
    iIntros (Φ) "!# (%Haddrs & %Hrepid & Hprotos & Hskt & Hfr & Htoken) HΦ".
    rewrite /prod_init.
    wp_pures. wp_lam. wp_pures.
    wp_apply ("Hinit" with "[$Hprotos $Htoken $Hskt $Hfr]").
    { do 2 (iSplit; first done). iApply prod_crdt_fun_spec; done. }
    iIntros (get update) "(HLS & Hget & Hupdate)".
    wp_pures.
    iApply "HΦ"; iFrame.
  Qed.

End prod_proof.
