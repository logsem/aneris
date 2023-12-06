From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fuel_ext resources.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth auth gmap gset excl.
From iris.bi Require Import bi.
From trillium.fairness Require Import lm_fair. 
From trillium.fairness.ext_models Require Import ext_models.
From trillium.fairness.examples.comp Require Import lib lib_ext client_defs.
From trillium.fairness.heap_lang Require Export lang.

Close Scope Z_scope.

  (* TODO: move *)
  Lemma set_filter_equiv:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A}
    {LL: LeibnizEquiv C}
    {FS: FinSet A C}
    (P1 P2 : A → Prop)
    (DEC1: ∀ x : A, Decision (P1 x)) (DEC2: ∀ x : A, Decision (P2 x))
    (P_EQ: forall x, P1 x <-> P2 x)
    (c1 c2: C)
    (EQUIV: c1 ≡ c2)
    ,
    filter P1 c1 = filter P2 c2.
  Proof. set_solver. Qed.

  (* TODO: move *)
  Lemma set_filter_and:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A}
    {LL: LeibnizEquiv C}
    {FS: FinSet A C}
    (P1 P2 : A → Prop)
    (DEC1: ∀ x : A, Decision (P1 x)) (DEC2: ∀ x : A, Decision (P2 x))
    (c: C)
    ,
    filter P1 (filter P2 c) = filter (fun x => P1 x /\ P2 x) c.
  Proof. set_solver. Qed. 

  (* TODO: move *)
  Lemma set_filter_comm:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A}
    {LL: LeibnizEquiv C}
    {FS: FinSet A C}
    (P1 P2 : A → Prop)
    (DEC1: ∀ x : A, Decision (P1 x)) (DEC2: ∀ x : A, Decision (P2 x))
    (c: C)
    ,
    filter P1 (filter P2 c) = filter P2 (filter P1 c). 
  Proof. set_solver. Qed. 

  (* TODO: move *)
  Lemma filter_singleton_if:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A},
    FinSet A C
    → ∀ (P : A → Prop) {H7 : ∀ x : A, Decision (P x)} (x : A),
        filter P ({[x]} : C) ≡ if decide (P x) then {[x]} else ∅.
  Proof. intros. destruct decide; set_solver. Qed. 


Section LibPMP. 
  Context `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM} {cpG: clientPreGS Σ}.
  Context `{PMPP: @PartialModelPredicatesPre (locale heap_lang) _ _ Σ client_model_impl}.

  Notation "'LSG' Einvs" := (LM_steps_gen Einvs (EM := EM) (iLM := client_model) (PMPP := PMPP) (eGS := heap_fairnessGS)) (at level 10).

  Tactic Notation "specialize_full" ident(H) :=
    let foo := fresh in
    evar (foo : Prop); cut (foo); subst foo; cycle 1; [eapply H|try clear H; intro H].

  Lemma live_roles_1 lb:
    live_roles client_model_impl (lb, 1) =
    if (decide (ρlg ∈ live_roles _ lb))
    then {[ ρ_lib ]}
    else if decide (ls_tmap lb (LM := lib_model lib_gs) !! ρlg = Some ∅)
         then {[ ρ_cl ]}
         else ∅.
  Proof.
    simpl. rewrite /client_lr.
    apply leibniz_equiv. rewrite !filter_union.

    erewrite filter_singleton_not with (x := ρ_ext). 
    2: { rewrite bool_decide_eq_false_2; [done| ].
         intros [? STEP]. inversion STEP. }
    rewrite union_empty_r. 

    destruct (decide (ρlg ∈ live_roles lf lb)) as [LR | LR].
    - pose proof (LM_live_role_map_notempty _ _ LR) as (?&MAP&?).
      erewrite filter_singleton, filter_singleton_not, decide_True.
      + set_solver.
      + eauto.
      + rewrite bool_decide_eq_false_2; [done| ].
        intros [? STEP]. inversion STEP. subst. set_solver.
      + rewrite bool_decide_eq_true_2; [done| ].
        eapply LM_live_roles_strong in LR as [? ?]. eauto.
        eexists. eapply ct_lib_step. simpl. eauto.
    - rewrite filter_singleton_not; [rewrite decide_False| ].
      2: { intros [DOM LIVE]%elem_of_filter.
           by apply LM_live_roles_strong in DOM. }
      2: { rewrite bool_decide_eq_false_2; [done| ].
           intros [? STEP]. inversion STEP. subst. simpl in LIB_STEP.
           destruct LR. apply LM_live_roles_strong. eauto. }
      destruct (ls_tmap lb (LM := lib_model lib_gs) !! ρlg) eqn:MAP0.
      (* ; rewrite MAP0. *)
      + destruct (decide (g = ∅)) as [-> | ?].
        * erewrite decide_True; [| done].
          rewrite filter_singleton; [set_solver| ].
          rewrite bool_decide_eq_true_2; [done| ]. eexists. by econstructor.
        * erewrite decide_False.
          2: { intros [=]. done. }
          rewrite filter_singleton_not; [set_solver| ].
          rewrite bool_decide_eq_false_2; [done| ].
          intros [? STEP]. inversion STEP. subst.
          rewrite MAP0 in LIB_NOROLES. congruence.
      + erewrite decide_False; [| done].
        rewrite filter_singleton_not; [set_solver| ].
        rewrite bool_decide_eq_false_2; [done| ].
        intros [? STEP]. inversion STEP. subst.
        rewrite MAP0 in LIB_NOROLES. congruence.
  Qed.

  Lemma live_roles_3 lb0:
    live_roles client_model_impl (lb0, 3) ≡ {[ ρ_cl ]}.
  Proof.
    simpl. rewrite /client_lr.
    rewrite !filter_union.
    erewrite filter_singleton_not, filter_singleton_not, filter_singleton; [set_solver| ..].
    - rewrite bool_decide_eq_true_2; [done| ]. eexists. econstructor.
    - apply not_true_iff_false.
      rewrite bool_decide_eq_false_2; [tauto| ].
      intros [? STEP]. inversion STEP.
    - apply not_true_iff_false.
      rewrite bool_decide_eq_false_2; [tauto| ].
      intros [? STEP]. inversion STEP.
  Qed.

  Lemma live_roles_0 lb:
    live_roles client_model_impl (lb, 0) = ∅.
  Proof.
    simpl. rewrite /client_lr.
    apply leibniz_equiv. rewrite !filter_union.
    erewrite !filter_singleton_not; [set_solver| ..].
    all: rewrite bool_decide_eq_false_2; [done| ].
    all: intros [? STEP]; inversion STEP.
  Qed.

  Lemma live_roles_2 lb:
    live_roles client_model_impl (lb, 2) =
    if (decide (lm_is_stopped ρlg lb))
    then {[ ρ_ext ]}
    else ∅.
  Proof.
    simpl. rewrite /client_lr.
    apply leibniz_equiv. rewrite !filter_union.
    rewrite union_comm.
    rewrite filter_singleton_not; [rewrite filter_singleton_not| ].
    2, 3: rewrite bool_decide_eq_false_2; [done| ]; 
    intros [? STEP]; by inversion STEP.
    rewrite !union_empty_l.

    unshelve erewrite set_filter_equiv with (P2 := fun r => r = ρ_ext /\ lm_is_stopped ρlg lb).
    5: reflexivity. 
    { intros. apply and_dec.
      - (* TODO: infer automatically *)
        destruct x, ρ_ext.
        { destruct e, e0.
          { destruct (decide (f = f0)); [left | right]; congruence. }
          3: destruct (decide (e = e0)); [left | right]; congruence.
          all: right; intros ?; congruence. }
        3: { destruct (y_EqDec y y0); [left | right]; congruence. }
        all: right; intros ?; congruence. 
      - solve_decision. }
    2: { intros. rewrite bool_decide_eq_true.
         split.
         - intros [? STEP]. inversion STEP. subst. split; eauto.
         - intros [-> STOP]. exists ((reset_lm_st ρlg lb ρlg_in_lib_gs), 1).
           by econstructor. }

    rewrite -set_filter_and set_filter_comm.
    erewrite set_filter_equiv.
    3: { rewrite filter_singleton; reflexivity. }
    2: { intros. apply iff_refl. }
    rewrite filter_singleton_if. 
    repeat destruct decide; reflexivity || tauto.
    Unshelve. intros. solve_decision. 
  Qed. 
    
  Lemma lib_tmap_dom_restricted (δ: fmstate lf):
    dom (ls_tmap δ (LM := lib_model lib_gs)) ⊆ {[ ρlg ]}.
  Proof.    
    done.
  Qed. 

  Lemma update_client_state `{clientGS Σ} Einvs
    (extr: execution_trace heap_lang) (mtr: auxiliary_trace M)
    c2 (lb lb': fmstate lf) f
    (LIB_STEP: locale_trans lb ρlg lb' (LM := lib_model lib_gs))
    (PROG_STEP: locale_step (trace_last extr) (Some 0) c2)
    (F_BOUND: f ≤ client_fl)
    :
    LSG Einvs ⊢
    em_msi (trace_last extr) (trace_last mtr) (em_GS0 := heap_fairnessGS) -∗
    partial_model_is (lb, 1) -∗
    partial_free_roles_are {[ρ_cl]} -∗
    has_fuels 0 {[ρ_lib := f]}
    ={Einvs}=∗
    ∃ (δ2 : M) (ℓ: mlabel M),
      ⌜em_valid_evolution_step (Some 0) c2 (trace_last mtr) ℓ δ2⌝ ∗
      em_msi c2 δ2 (em_GS0 := heap_fairnessGS) ∗
      has_fuels 0 (if decide (ls_tmap lb' (LM := lib_model lib_gs) !! ρlg = Some ∅)
                   then {[ρ_cl := client_fl]}
                   else {[ρ_lib := f]}) ∗
      partial_model_is (lb', 1) ∗
      partial_free_roles_are
      (if decide (ls_tmap lb' (LM := lib_model lib_gs) !! ρlg = Some ∅) then {[ρ_lib]} else {[ρ_cl]}).
  Proof.
    
    iIntros "#PMP MSI ST FR FUELS".
    Local Ltac dEq := destruct (decide (_ = _)).
    Local Ltac dEl := destruct (decide (_ ∈ _)).
    pose proof (LM_map_empty_notlive lb' ρlg (LF := (@lib_LF _ lib_gs_ne))).

    pose proof (live_roles_1 lb) as LIVE. rewrite decide_True in LIVE.
    2: { eapply LM_live_roles_strong. eexists. eauto. }
    (* TODO: consider the case with rem ≠ ∅ *)
    pose proof (live_roles_1 lb') as LIVE'.

    remember (trace_last extr) as c1. destruct c1 as (σ1, tp1).
    destruct c2 as (σ2, tp2).

    iPoseProof (LM_steps_gen_nofork_sub with "PMP") as "PMP'". 
    iPoseProof (update_step_still_alive_gen with "[$] [$] [$] [$] [$]") as "EM_STEP".
    7: { apply PROG_STEP. }
    7: { apply ct_lib_step. simpl. eauto. }
    { rewrite LIVE LIVE'.
      apply union_subseteq_l'.
      dEq; dEl; set_solver. }
    { rewrite dom_singleton.
      assert ((if (decide (ls_tmap lb' (LM := lib_model lib_gs) !! ρlg = Some ∅))
              then {[ ρ_lib ]}
              else (∅: gset (fmrole client_model_impl))) ⊆ {[ρ_lib]}) as IN.
      { dEq; set_solver. }
      apply IN. }
    { rewrite LIVE. set_solver. }
    all: eauto.
    { Unshelve.
      2: exact (if decide (ls_tmap lb' (LM := lib_model lib_gs) !! ρlg = Some ∅)
                then {[ ρ_cl := client_fl ]}
                else {[ ρ_lib := f ]}).
      destruct (decide (_=_)); set_solver. }
    { repeat split; rewrite ?LIVE ?LIVE'.
      - dEl.
        2: { destruct decide; set_solver. }
        intros _. rewrite decide_False.
        { rewrite lookup_singleton. simpl. lia. }
        tauto.
      - destruct (decide (_ ∈ _)); [set_solver| ].
        destruct (decide (_=_)); [set_solver| ].
        rewrite !lookup_singleton. simpl. lia.
      - set_solver.
      - dEq; [| set_solver].
        intros. assert (ρ' = ρ_cl) as -> by set_solver.
        rewrite lookup_singleton. simpl. lia.
      - dEq; set_solver.
      - dEq; dEl; set_solver.
      - dEq; dEl; set_solver. }
    { red. intros. red.
      (* TODO: move this simplification, as it occurs quite often *)
      rewrite /update_mapping. rewrite map_imap_dom_eq.
      2: { rewrite dom_gset_to_gmap. intro.
           destruct (decide (k ∈ dom R)); [| done].
           intros. by eapply elem_of_dom. }
      rewrite dom_gset_to_gmap. intros g' IN'.
      red in H2.
      (* at this point we must ensure that no new group roles  *)
(*          were created by a lib step *)

      destruct IN' as [? IN']. simpl in IN'.
      apply (ls_mapping_tmap_corr (LM := lib_model lib_gs)) in IN' as (?&?&?).
      pose proof (lib_tmap_dom_restricted lb') as DOML.
      specialize (DOML g'). specialize_full DOML.
      { apply elem_of_dom. set_solver. }
      apply elem_of_singleton_1 in DOML. subst g'.
      rewrite decide_False; [set_solver| ].
      intros EMP. set_solver. }
      
    rewrite LIVE LIVE'.
    iMod "EM_STEP" as (??) "(?&?&?&?&FREE)".
    iModIntro. do 2 iExists _. iFrame.
    
    iApply partial_free_roles_are_Proper; [| iFrame].
    dEl; dEq; tauto || set_solver.
  Qed.

  (* TODO: unify with model_agree ? *)
  Lemma y_model_agree `{clientGS Σ} y1 y2:
    ⊢ y_auth_model_is y1 -∗ y_frag_model_is y2 -∗ ⌜y1 = y2⌝.
  Proof.
    iIntros "Ha Hf".
    by iDestruct (own_valid_2 with "Ha Hf") as
      %[Heq%Excl_included%leibniz_equiv ?]%auth_both_valid_discrete.
  Qed.

  (* TODO: unify with update_model ? *)
  Lemma y_update_model `{clientGS Σ} y1 y2 y:
    y_auth_model_is y1 -∗ y_frag_model_is y2 ==∗ y_auth_model_is y ∗ y_frag_model_is y.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "[??]" ; eauto.
    - by apply auth_update, option_local_update, (exclusive_local_update _ (Excl y)).
    - iModIntro. iFrame.
  Qed.
     
(*   Lemma big_opM_fmap': *)
(*   ∀ {M M' : ofe} {o : M → M → M} {o' : M' → M' → M'} *)
(*     {Monoid0 : Monoid o} {Monoid0' : Monoid o'} {K : Type} *)
(*     {EqDecision0 : EqDecision K} {H : Countable K} *)
(*     (f : M → M') (m : gmap K M), *)
(*     (([^ op map] k↦y ∈ m, f <$> ({[ k := y ]}: gmap K M)): gmap K M') = (f <$> m: gmap K M'). *)
(* (* f <$> {[k := ]} *) *)


  (* TODO: remove tid=0 restriction ? *)
  Let lib_pmi `{clientGS Σ} (m: gmap (locale heap_lang) (gset (fmrole lib_model_impl))): iProp Σ:=
    (∃ (L: gset (fmrole lib_model_impl)) (Ract Rfr: gset client_role),
        ⌜ m = {[ 0 := L ]} ⌝ ∗
         frag_mapping_is {[ ρlg := L ]} ∗
         (⌜ L ≠ ∅ ⌝ ∗ ⌜ Ract = {[ ρ_lib ]} /\ Rfr = {[ ρ_cl ]} ⌝ ∗ (∃ f: nat, partial_fuel_is {[ ρ_lib := f ]} ∗ ⌜ 1 <= f <= client_fl ⌝) ∨
          ⌜ L = ∅ ⌝ ∗ ⌜ Ract = {[ ρ_cl ]} /\ Rfr = {[ ρ_lib ]} ⌝ ∗ partial_fuel_is {[ inr ρy := client_fl ]}) ∗
        partial_mapping_is {[ 0 := Ract ]} ∗
        partial_free_roles_are Rfr ∗
        y_frag_model_is 1).
  
  Definition lib_PMPP `{clientGS Σ}:
    @PartialModelPredicatesPre (locale heap_lang) _ _ Σ lib_model_impl.
   refine
    {|
        partial_model_is := frag_model_is;
        partial_free_roles_are := frag_free_roles_are;
        partial_fuel_is := frag_fuel_is;
        partial_mapping_is := lib_pmi;
    |}.
  Unshelve.
  all: try (apply _ || solve_proper).
  (* TODO: reuse proofs from resources.v *)
  - intros.
    rewrite /frag_fuel_is.
    rewrite map_fmap_union. rewrite -gmap_disj_op_union.
    2: { by apply map_disjoint_fmap. }
    by rewrite auth_frag_op own_op.
  - intros. rewrite /frag_free_roles_are.
    rewrite -gset_disj_union; auto.
    by rewrite auth_frag_op own_op.
  - iApply own_unit.
  Defined.

  Lemma lib_open_inv `{clientGS Σ} ζ fs (FSnz : fs ≠ ∅):
    client_inv -∗ has_fuels ζ fs (PMPP := lib_PMPP) -∗
    |={↑Ns, ∅}=>
    ⌜ ζ = 0 ⌝ ∗
    (∃ lb, partial_model_is (lb, 1) (PartialModelPredicatesPre := PMPP) ∗ model_state_interp lb) ∗
    frag_mapping_is {[ρlg := dom fs]}  ∗ y_auth_model_is 1 ∗
    (∃ f, partial_fuel_is {[ρ_lib := f]} ∗ ⌜ 1 <= f <= client_fl ⌝) ∗
    partial_mapping_is {[0 := {[ρ_lib]}]} ∗
    partial_free_roles_are {[inr ρy]} ∗ y_frag_model_is 1 ∗
    frag_fuel_is fs ∗
    (▷ (∃ st, client_inv_impl st) ={ ∅, ↑Ns}=∗ emp).
  Proof.
    iIntros "#INV FUELS_LIB".
    iInv Ns as ((lb, y)) ">(ST & YST_AUTH & inv')" "CLOS".
    rewrite difference_diag_L. iModIntro.
    iDestruct (has_fuels_equiv with "FUELS_LIB") as "[MAP_LIB FUEL_LIB]".
    simpl. iDestruct "MAP_LIB" as (???) "(%LIBM&LM&MATCH&MAP&FR&YST)".
    assert (ζ = 0 /\ L = dom fs) as [-> ->]; [| clear LIBM].
    { by apply map_singleton_inj in LIBM as [-> <-]. }
    (* assert (S <$> fs ≠ ∅) by (by intros ?%fmap_empty_inv). *)
    iDestruct "MATCH" as "[(_&[-> ->]&(%f & Ff & %BOUND)) | [% _]]".
    2: { exfalso. apply FSnz. apply dom_empty_iff. set_solver. }
    iPoseProof (y_model_agree with "YST_AUTH YST") as "->".
    iPoseProof (frag_mapping_same with "[inv'] LM") as "%TMAP0".
    { iDestruct "inv'" as (?)"(?&?&?)". iFrame. }
    iPoseProof (frag_fuel_included with "[inv'] [FUEL_LIB]") as "%FUEL0".
    { iDestruct "inv'" as (?)"(?&?&?&?)". iFrame. }
    { iApply frag_fuel_is_big_sepM; [done | by iFrame]. }
    iSplitR; [done| ].
    iFrame. iSplitL "ST inv'".
    - iExists lb. iFrame. 
    - iDestruct (frag_fuel_is_big_sepM with "FUEL_LIB") as "?"; [done| ].
      iFrame. iExists _. iFrame. done.
  Qed.

  (* TODO: move*)
  From trillium.fairness Require Import actual_resources.

  Lemma fuel_keep_step_lifting `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns):
  LSG Einvs ∗ client_inv ⊢
  ∀ (extr : execution_trace heap_lang) (auxtr : auxiliary_trace M)
    (c2 : cfg heap_lang) (fs : gmap (fmrole lib_model_impl) nat)
    (ζ : locale heap_lang) (_ : dom fs ≠ ∅) (_ : locale_step
                                                   (trace_last extr)
                                                   (Some ζ) c2),
    has_fuels ζ (S <$> fs) (PMPP := lib_PMPP) -∗
    em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := heap_fairnessGS)
    ={Einvs ∪ ↑Ns}=∗
    ∃ (δ2 : M) (ℓ : mlabel M),
      ⌜em_valid_state_evolution_fairness (extr :tr[ Some ζ ]: c2)
         (auxtr :tr[ ℓ ]: δ2)⌝ ∗
      has_fuels ζ (filter (λ '(k, _), k ∈ dom fs ∖ ∅) fs) (PMPP := lib_PMPP) ∗
      em_msi c2 δ2 (em_GS0 := heap_fairnessGS).
  Proof.
    iIntros "[#PMP #COMP]". iIntros "* FUELS_LIB MSI". simpl in *.
    
    assert (S <$> fs ≠ ∅) as NE.
    { intros ?%dom_empty_iff. set_solver. }

    iPoseProof (lib_open_inv with "[$] FUELS_LIB") as "INV'"; [set_solver| ].
    rewrite union_comm_L.
    iMod (fupd_mask_frame_r _ _ Einvs with "INV'") as
      "(-> & (%lb & ST & inv') & LM & YST_AUTH & (%f & Ff & %BOUND) & MAP & FR & YST & FUEL_LIB & CLOS)"; [set_solver| ].

    
    iMod (actual_update_no_step_enough_fuel_keep with "[LM FUEL_LIB] inv'") as (lb') "(%LIB_STEP & FUELS_LIB & MSI_LIB & %TMAP_LIB)".
    (* 3: { apply empty_subseteq. } *)
    { eauto. }
    { clear. red. intros. done. }
    { rewrite /has_fuels_S. rewrite has_fuels_equiv. iFrame.
      iApply frag_fuel_is_big_sepM; done. }
    
    destruct (trace_last extr) as (σ1, tp1) eqn:LASTE. destruct c2 as (σ2, tp2).
    rewrite LASTE.
    rewrite difference_empty_L.
    (* rewrite difference_empty_L in TMAP_LIB. *)
    iAssert (has_fuels 0 {[ ρ_lib := f ]}) with "[MAP Ff]" as "FUELS".
    { rewrite /has_fuels. rewrite dom_singleton_L big_sepS_singleton.
      rewrite lookup_singleton. iFrame. iExists _. iFrame. done. }

    rewrite -LASTE.
    iPoseProof (update_client_state with "[$] [$] [$] [$] [$]") as "EM_STEP"; eauto.
    { eexists. split; [apply LIB_STEP| ]. done. }
    { lia. }
    iMod (fupd_mask_mono with "EM_STEP") as (δ2 ℓ) "(EV & MSI & FUELS & ST & FR)"; [set_solver| ].
    do 2 iExists _. iFrame "EV MSI".
    rewrite gmap_filter_dom_id. 

    iDestruct ("CLOS" with "[ST MSI_LIB YST_AUTH]") as "CLOS".
    { iNext. iExists (_, _). rewrite /client_inv_impl. iFrame. }
    iMod (fupd_mask_frame_r _ _ Einvs with "CLOS") as "_"; [set_solver| ].

    iModIntro.
    iDestruct "FUELS" as "[MAP FUEL]". iDestruct "FUELS_LIB" as "[MAP_LIB FUELS_LIB]".
    rewrite /has_fuels. iSplitR "FUELS_LIB".
    2: { done. }
    simpl. 
    rewrite /lib_pmi. do 3 iExists _. iFrame.
    iSplitR; [done| ].
    (* TODO: case when domain becomes empty *)
    iLeft. iSplitR; [done| ].
    rewrite TMAP_LIB.
    (* rewrite lookup_insert. *)

    assert (ls_tmap lb (LM := lib_model lib_gs) !! ρlg ≠ Some ∅) as TM_NE.
    { edestruct (locale_trans_ex_role lb ρlg lb' (LM := lib_model lib_gs)) as [? STEP].
      { eexists. split; [apply LIB_STEP| ]. done. }
    eapply ls_mapping_tmap_corr in STEP as (?&?&?). rewrite H1. set_solver. } 
    
    repeat erewrite @decide_False; try done. 
    iSplitR.
    - iPureIntro.  set_solver.
    - rewrite dom_singleton_L big_sepS_singleton.
      rewrite lookup_singleton.
      iDestruct "FUEL" as (?) "[%EQ ?]". inversion EQ. subst.
      iExists _. iFrame. iPureIntro. lia.
  Qed.

  Lemma lib_fuel_drop_step_preserves_LSI s rem:
    fuel_drop_preserves_LSI s rem (LSI := LSI_groups_fixed lib_gs).
  Proof. 
    (* done. *)
    red. intros. red. intros ?? IN.
    apply map_filter_lookup_Some in IN as [??].
    eapply H0; eauto. 
  Qed. 
    

  (* TODO: move*)
  Lemma fuel_drop_step_lifting `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns):
  LSG Einvs ∗ client_inv ⊢
  ∀ (extr : execution_trace heap_lang) (auxtr : auxiliary_trace M)
    (c2 : cfg heap_lang) s (fs : gmap (fmrole lib_model_impl) nat)
    rem
    (ζ : locale heap_lang) (_ : dom fs ≠ ∅)

    (_: (live_roles _ s) ∩ rem = ∅)
    (_: rem ⊆ dom fs)
    (_ : locale_step (trace_last extr) (Some ζ) c2),
    has_fuels ζ (S <$> fs) (PMPP := lib_PMPP) -∗
    partial_model_is s -∗
    em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := heap_fairnessGS)
    ={Einvs ∪ ↑Ns}=∗
    ∃ (δ2 : M) (ℓ : mlabel M),
      ⌜em_valid_state_evolution_fairness (extr :tr[ Some ζ ]: c2)
         (auxtr :tr[ ℓ ]: δ2)⌝ ∗
      has_fuels ζ (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs) (PMPP := lib_PMPP) ∗
      partial_model_is s ∗
      em_msi c2 δ2 (em_GS0 := heap_fairnessGS).
  Proof.
    iIntros "[#PMP #COMP]". iIntros "* FUELS_LIB ST_LIB MSI". simpl in *.
    
    assert (S <$> fs ≠ ∅) as NE.
    { intros ?%dom_empty_iff. set_solver. }

    iPoseProof (lib_open_inv with "[$] FUELS_LIB") as "INV'"; [set_solver| ].
    rewrite union_comm_L.
    iMod (fupd_mask_frame_r _ _ Einvs with "INV'") as
      "(-> & (%lb & ST & inv') & LM & YST_AUTH & (%f & Ff & %BOUND) & MAP & FR & YST & FUEL_LIB & CLOS)"; [set_solver| ].

    iAssert (⌜ s = ls_under lb ⌝)%I as %->.
    { rewrite /model_state_interp.
      iDestruct "inv'" as (?)"(?&?&?&ST_LIB'&?)".
      (* TODO: make a lemma? *)
      by iDestruct (own_valid_2 with "ST_LIB' ST_LIB") as
      %[Heq%Excl_included%leibniz_equiv ?]%auth_both_valid_discrete. }
      
      
    iMod (actual_update_no_step_enough_fuel_drop with "[LM FUEL_LIB] ST_LIB inv'") as (lb') "(%LIB_STEP & FUELS_LIB & ST_LIB & MSI_LIB & %TMAP_LIB)".
    (* 3: { apply empty_subseteq. } *)
    { eauto. }
    4: { rewrite /has_fuels_S. rewrite has_fuels_equiv. iFrame.
         iApply frag_fuel_is_big_sepM; done. }
    2: { eauto. }
    { done. }
    { apply lib_fuel_drop_step_preserves_LSI. }
    
    destruct (trace_last extr) as (σ1, tp1) eqn:LASTE. destruct c2 as (σ2, tp2).
    rewrite LASTE.
    (* rewrite difference_empty_L. *)
    (* rewrite difference_empty_L in TMAP_LIB. *)
    iAssert (has_fuels 0 {[ ρ_lib := f ]}) with "[MAP Ff]" as "FUELS".
    { rewrite /has_fuels. rewrite dom_singleton_L big_sepS_singleton.
      rewrite lookup_singleton. iFrame. iExists _. iFrame. done. }

    rewrite -LASTE.
    iPoseProof (update_client_state with "[$] [$] [$] [$] [$]") as "EM_STEP"; eauto.
    { eexists. split; [apply LIB_STEP| ]. done. }
    { lia. }
    iMod (fupd_mask_mono with "EM_STEP") as (δ2 ℓ) "(EV & MSI & FUELS & ST & FR)"; [set_solver| ].
    do 2 iExists _. iFrame "EV MSI".

    iDestruct ("CLOS" with "[ST MSI_LIB YST_AUTH]") as "CLOS".
    { iNext. iExists (_, _). rewrite /client_inv_impl. iFrame. }
    iMod (fupd_mask_frame_r _ _ Einvs with "CLOS") as "_"; [set_solver| ].

    iModIntro.
    iDestruct "FUELS" as "[MAP FUEL]". iDestruct "FUELS_LIB" as "[MAP_LIB FUELS_LIB]".

    iFrame "ST_LIB". 
    iSplitR "FUELS_LIB".
    2: { rewrite dom_domain_restrict; [| set_solver]. done. }
    simpl. rewrite dom_domain_restrict; [| set_solver].
    rewrite /lib_pmi. do 3 iExists _. iFrame.
    iSplitR; [done| ].

    rewrite TMAP_LIB. rewrite lookup_insert.
    destruct (decide (dom fs = rem)).
    2: { 

    iLeft.
    iSplitR.
    { iPureIntro. intros ?. apply n. set_solver. } 
    (* rewrite lookup_insert. *)
    repeat erewrite @decide_False with (P := (Some (dom fs ∖ rem) = Some ∅)).
    (* 2-3: by intros [=]. *)
    2, 3: intros [=]; set_solver. 
    iSplitR.
    { iPureIntro. set_solver. }
    rewrite dom_singleton_L big_sepS_singleton.
    rewrite lookup_singleton.
    iDestruct "FUEL" as (?) "[%EQ ?]". inversion EQ. subst.
    iExists _. iFrame. iPureIntro. lia. }
    
    subst rem. iRight. iSplitR.
    { iPureIntro. set_solver. }
    rewrite difference_diag_L. repeat erewrite decide_True.
    2, 3: done.
    iSplitR.
    { iPureIntro. set_solver. }
    rewrite dom_singleton_L big_sepS_singleton.
    rewrite lookup_singleton.
    iDestruct "FUEL" as (?) "[%EQ ?]". inversion EQ.
    iFrame.         
  Qed.


  Lemma lib_model_step_preserves_LSI:
  ∀ (s1 : lib_model_impl) (ρ : fmrole lib_model_impl) 
    (s2 : lib_model_impl) (fs1 fs2 : gmap (fmrole lib_model_impl) nat),
    model_step_preserves_LSI s1 ρ s2 fs1 fs2 (LSI := LSI_groups_fixed lib_gs).
  Proof.
    (* done.  *)
    (* can be proven trivially, but the proof below should work for non-trivial Gs *)
    intros. red. intros. red. intros ??.
    rewrite /update_mapping. rewrite map_lookup_imap. simpl.
    rewrite lookup_gset_to_gmap.
    rewrite option_guard_decide.
    destruct (decide (ρ0 ∈ _ ∖ _)); simpl. 
    2: { congruence. }
    destruct decide.
    { eapply H0; eauto. }
    intros [=->]. eapply H0; eauto.
  Qed.
    
  Lemma model_step_lifting `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns):
  LSG Einvs ∗ client_inv ⊢
  ∀ (extr : execution_trace heap_lang) (auxtr : auxiliary_trace M)
    (tp1 tp2 : list (language.expr heap_lang)) (σ1 σ2 : language.state heap_lang)
    (s1 s2 : lib_model_impl) (fs1 fs2 : gmap (fmrole lib_model_impl) nat)
    (ρ : fmrole lib_model_impl) (δ1 : M) (ζ : locale heap_lang)
    (fr1 fr_stash : gset (fmrole lib_model_impl))
    (_ : live_roles lib_model_impl s2 ∖ live_roles lib_model_impl s1 ⊆ fr1 ∪ dom fs1 ∩ dom fs2)
    (_ : fr_stash ⊆ dom fs1) (_ : live_roles lib_model_impl s1
                                  ∩ (fr_stash ∖ {[ρ]}) = ∅)
    (_ : dom fs2 ∩ fr_stash = ∅) (_ : trace_last extr = (tp1, σ1))
    (_ : trace_last auxtr = δ1) (_ : locale_step (tp1, σ1) (Some ζ) (tp2, σ2))
    (_ : fmtrans lib_model_impl s1 (Some ρ) s2)
    (_ : valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := lib_model lib_gs))
  ,
    has_fuels ζ fs1 (PMPP := lib_PMPP) -∗
    partial_model_is s1 (PartialModelPredicatesPre := lib_PMPP) -∗
    em_msi (tp1, σ1) δ1 (em_GS0 := heap_fairnessGS) -∗
    partial_free_roles_are fr1 (PartialModelPredicatesPre := lib_PMPP)
    ={Einvs ∪ ↑Ns}=∗
    ∃ (δ2 : M) (ℓ : mlabel M),
      ⌜em_valid_state_evolution_fairness (extr :tr[ Some ζ ]: (tp2, σ2))
         (auxtr :tr[ ℓ ]: δ2)⌝ ∗
      has_fuels ζ fs2 (PMPP := lib_PMPP) ∗
      partial_model_is s2 (PartialModelPredicatesPre := lib_PMPP) ∗
      em_msi (tp2, σ2) δ2 (em_GS0 := heap_fairnessGS) ∗
      partial_free_roles_are
        (fr1 ∖ (live_roles lib_model_impl s2 ∖ (live_roles lib_model_impl s1 ∪ dom fs1 ∩ dom fs2))
         ∪ fr_stash) (PartialModelPredicatesPre := lib_PMPP).
  Proof.
    iIntros "[#PMP #COMP]". iIntros "* FUELS_LIB ST_LIB MSI FR_LIB". simpl in *.
    
    assert (ρ ∈ dom fs1) as DOM1ρ by apply x7.
    assert (dom fs1 ≠ ∅ /\ fs1 ≠ ∅) as [FS1nz FS1nz'].
    { split; intros ?; set_solver. }
    
    iPoseProof (lib_open_inv with "[$] FUELS_LIB") as "INV'"; [done| ].
    rewrite union_comm_L.
    iMod (fupd_mask_frame_r _ _ Einvs with "INV'") as
      "(-> & (%lb & ST & inv') & LM & YST_AUTH & (%f & Ff & %BOUND) & MAP & FR & YST & FUEL_LIB & CLOS)"; [set_solver| ].

    iPoseProof (LM_steps_gen_nofork_sub with "PMP") as "PMP'".
    iMod (actual_update_step_still_alive_gen with "[LM FUEL_LIB] [$] [$] [$]") as "LIFT"; eauto.
    2: { rewrite has_fuels_equiv. iFrame. iApply frag_fuel_is_big_sepM; done. }
    { apply lib_model_step_preserves_LSI. }

    iDestruct "LIFT" as (lb') "(%LIB_STEP & FUELS_LIB & ST_LIB & MSI_LIB & FR_LIB & %TMAP_LIB)".
    simpl. iFrame "ST_LIB".
    
    iAssert (has_fuels 0 {[ ρ_lib := f ]}) with "[MAP Ff]" as "FUELS".
    { rewrite /has_fuels. rewrite dom_singleton_L big_sepS_singleton.
      rewrite lookup_singleton. iFrame. iExists _. iFrame. done. }

    rewrite -x3 -x4. rewrite -x3 in x5.
    iPoseProof (update_client_state with "[$] [MSI] [ST] [$] [$]") as "EM_STEP"; eauto.
    { eexists. split; [apply LIB_STEP| ]. done. }
    { lia. }
    iMod (fupd_mask_mono with "EM_STEP") as (δ2 ℓ) "(EV & MSI & FUELS & ST & FR)"; [set_solver| ].
    do 2 iExists _. iFrame "EV MSI".

    iDestruct ("CLOS" with "[ST MSI_LIB YST_AUTH]") as "CLOS".
    { iNext. iExists (_, _). rewrite /client_inv_impl. iFrame. }
    iMod (fupd_mask_frame_r _ _ Einvs with "CLOS") as "_"; [set_solver| ].
    iModIntro.

    rewrite !has_fuels_equiv. simpl.
    iDestruct "FUELS" as "[MAP FUELS]".
    iDestruct "FUELS_LIB" as "[MAP' FUELS_LIB]". iFrame "FUELS_LIB FR_LIB".
    rewrite /lib_pmi. do 3 iExists _. iFrame.
    iSplitR; [done |].
    rewrite TMAP_LIB. rewrite lookup_insert.
    dEq.
    - iRight. rewrite big_sepM_singleton. iFrame.
      iPureIntro. set_solver.
    - iLeft. rewrite big_sepM_singleton.
      iApply bi.sep_assoc. iSplitR "FUELS".
      2: { iExists _. iFrame. iPureIntro. lia. }
      iPureIntro. split; [| set_solver]. intros ?. rewrite H1 in n. done.
  Qed.


  Lemma lib_PMP `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns):
    LSG Einvs ∗ client_inv ⊢
    (* PartialModelPredicates (Einvs ∪ ↑Ns) (LM := LM) (iLM := spinlock_model) (PMPP := (sl1_PMPP γ)).  *)
    LM_steps_gen_nofork (Einvs ∪ ↑Ns) (EM := EM) (iLM := lib_model lib_gs) (PMPP := lib_PMPP) (eGS := heap_fairnessGS).
  Proof.
    iIntros "[#PMP #COMP]". iApply @Build_LM_steps_gen_nofork.

    iModIntro. repeat iSplitR.
    - iIntros "* FUELS_LIB ST MSI".
      iDestruct (fuel_drop_step_lifting with "[$] [] [] [] [] FUELS_LIB ST MSI") as "LIFT"; eauto.
      (* change the PMP interface so it allows fupd in fuel step *)
      admit.      
    - iIntros "* FUELS_LIB MSI".
      iDestruct (fuel_keep_step_lifting with "[$] [] [] FUELS_LIB MSI") as "LIFT"; eauto.
      (* same as above *)
      admit.
    - iIntros "* FUELS_LIB ST MSI FR".
      iApply (model_step_lifting with "[$] [] [] [] [] [] [] [] [] [] [$] [$] [$] [$]"); eauto.
  Admitted.


End LibPMP. 
