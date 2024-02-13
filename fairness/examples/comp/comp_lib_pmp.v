From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import resources.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth auth gmap gset excl.
From iris.bi Require Import bi.
From trillium.fairness Require Import lm_fair. 
From trillium.fairness.ext_models Require Import ext_models.
From trillium.fairness.examples.comp Require Import lib lib_ext client_defs tracker.
From trillium.fairness.heap_lang Require Export lang.
From trillium.fairness Require Import actual_resources.

Close Scope Z_scope.


Section LibPMP. 
  Context `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM} {cG: clientGS Σ}.
  Context `{PMPP: @PartialModelPredicatesPre (locale heap_lang) _ _ Σ client_model_impl}.
  Context {relies_on_cl: locale heap_lang -> locale heap_lang -> iProp Σ}. 
  Notation " τ '⤞_cl' g" := (relies_on_cl τ g) (at level 20). 

  Notation "'LSG' Einvs" := (LM_steps_gen Einvs (EM := EM) (iLM := client_model) (PMPP := PMPP) (eGS := heap_fairnessGS) (relies_on := relies_on_cl)) (at level 10).

  Tactic Notation "specialize_full" ident(H) :=
    let foo := fresh in
    evar (foo : Prop); cut (foo); subst foo; cycle 1; [eapply H|try clear H; intro H].

  Lemma lib_tmap_dom_restricted (δ: fmstate lf):
    dom (ls_tmap δ) ⊆ {[ ρlg ]}.
  Proof.    
    done.
  Qed. 

  (* TODO: move *)
  Lemma ite_neg `{Decision P} {A: Type} (x y : A):
    (if decide (¬ P) then x else y) = if decide P then y else x.
  Proof.
    symmetry. destruct decide.
    - rewrite decide_False; [done| ]. tauto.
    - by rewrite decide_True. 
  Qed.


  (* TODO: need to generalize enabled_group_singleton this way
     and show that for such LMs fair_by_group and usual fair are the same.
     Then we can get rid of this part of client LSI *)
  Definition enabled_group_singleton_gen :=
    forall δ g, role_enabled_model (g: fmrole lf) δ <-> default ∅ (ls_tmap δ !! g) ≠ ∅.

  Lemma egsg_lib: enabled_group_singleton_gen.
  Proof. Admitted. 

  Lemma update_client_state tid g_cl Einvs
    (extr: execution_trace heap_lang) (mtr: auxiliary_trace M)
    c2 (lb lb': fmstate lf) f
    (LIB_STEP: locale_trans lb ρlg lb' (LM := lib_model lib_gs))
    (PROG_STEP: locale_step (trace_last extr) (Some tid) c2)
    (F_BOUND: f ≤ client_fl)
    (dis' := ¬ role_enabled_model (ρlg: fmrole lf) lb')
    :
    LSG Einvs ⊢
    em_msi (trace_last extr) (trace_last mtr) (em_GS0 := heap_fairnessGS) -∗
    partial_model_is (lb, 1) -∗
    partial_free_roles_are {[ρ_cl]} -∗
    tid ⤞_cl g_cl -∗
    has_fuels g_cl {[ρ_lib := f]}
    ={Einvs}=∗    
    ∃ (δ2 : M) (ℓ: mlabel M),
      ⌜em_valid_evolution_step (Some tid) c2 (trace_last mtr) ℓ δ2⌝ ∗
      em_msi c2 δ2 (em_GS0 := heap_fairnessGS) ∗
      tid ⤞_cl g_cl ∗
      has_fuels g_cl (if decide dis'
                   then {[ρ_cl := client_fl]}
                   else {[ρ_lib := f]}) ∗
      partial_model_is (lb', 1) ∗
      partial_free_roles_are
      (if decide dis' then {[ρ_lib]} else {[ρ_cl]}).
  Proof.    
    iIntros "#PMP MSI ST FR RON FUELS".
    Local Ltac dEq := destruct (decide (_ = _)).
    Local Ltac dEl := rewrite ?ite_neg; unfold role_enabled_model; destruct (decide (_ ∈ _)).
    (* subst dis'.  *)

    pose proof (LM_map_empty_notlive lb' ρlg (LF := (@lib_LF _ lib_gs_ne))) as EMP_NL. 

    pose proof (live_roles_1 lb) as LIVE. rewrite decide_True in LIVE.
    2: { eapply LM_live_roles_strong. eexists. eauto. }
    (* TODO: consider the case with rem ≠ ∅ *)
    pose proof (live_roles_1 lb') as LIVE'.

    remember (trace_last extr) as c1. destruct c1 as (σ1, tp1).
    destruct c2 as (σ2, tp2).

    iPoseProof (LM_steps_gen_nofork_sub with "PMP") as "PMP'". 
    iPoseProof (update_step_still_alive_gen with "[$] [$] [$] [$] [$] [$]") as "EM_STEP".
    7: { apply PROG_STEP. }
    7: { apply ct_lib_step. simpl. eauto. }
    { rewrite LIVE LIVE'.
      apply union_subseteq_l'.
      dEl; set_solver. }
    { rewrite dom_singleton.
      assert ((if (decide dis')
              then {[ ρ_lib ]}
              else (∅: gset (fmrole client_model_impl))) ⊆ {[ρ_lib]}) as IN.
      { dEl; set_solver. }
      apply IN. }
    { rewrite LIVE. set_solver. }
    all: eauto.
    { Unshelve.
      2: exact (if decide dis'
                then {[ ρ_cl := client_fl ]}
                else {[ ρ_lib := f ]}).
      dEl; set_solver. }
    { repeat split; rewrite ?LIVE ?LIVE';  clear -F_BOUND EMP_NL. 
      - dEl.
        2: { set_solver. }
        intros _.
        rewrite lookup_singleton. simpl. lia. 
      - dEl; set_solver. 
      - set_solver.
      - dEl; [set_solver| ].
        intros. assert (ρ' = ρ_cl) as -> by set_solver.
        rewrite lookup_singleton. simpl. lia.
      - dEl; set_solver.
      - dEl; set_solver.
      - dEl; set_solver. }
    { red. simpl. intros. red. 
      simpl. intros g' [? IN'].
      apply ls_mapping_tmap_corr in IN' as (?&TM'&?).
      pose proof (lib_tmap_dom_restricted lb') as DOML.
      specialize (DOML g'). specialize_full DOML.
      { apply elem_of_dom. eauto. }
      apply elem_of_singleton in DOML. subst g'.
      rewrite decide_False.
      2: { apply P_NNP. apply egsg_lib. rewrite TM'. set_solver. }
      rewrite /mapped_roles. apply flatten_gset_spec.
      exists ({[ ρ_lib ]}). split; [| apply elem_of_singleton; reflexivity].
      rewrite elem_of_map_img. exists g.
      by rewrite lookup_insert dom_singleton_L. }
      
    rewrite LIVE LIVE'.
    iMod "EM_STEP" as (??) "(?&?&?&?&?&FREE)".
    iModIntro. do 2 iExists _. iFrame.
    
    iApply partial_free_roles_are_Proper; [| iFrame].
    (* clear -H1.  *)
    dEl; tauto || set_solver.
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
     
  
  Definition lib_PMPP `{clientGS Σ}:
    @PartialModelPredicatesPre lib_grole _ _ Σ lib_model_impl.
   refine
    {|
        partial_model_is := frag_model_is;
        partial_free_roles_are := frag_free_roles_are;
        partial_fuel_is := frag_fuel_is;
        partial_mapping_is := partial_mapping_is;
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

  (* Let lib_pmi `{clientGS Σ} (m: gmap (locale heap_lang) (gset (fmrole lib_model_impl))): iProp Σ:= *)
  (*   (∃ (L: gset (fmrole lib_model_impl)) (Ract Rfr: gset client_role), *)
  (*       ⌜ m = {[ 0 := L ]} ⌝ ∗ *)
  (*        frag_mapping_is {[ ρlg := L ]} ∗ *)
  (*        (⌜ L ≠ ∅ ⌝ ∗ ⌜ Ract = {[ ρ_lib ]} /\ Rfr = {[ ρ_cl ]} ⌝ ∗ (∃ f: nat, partial_fuel_is {[ ρ_lib := f ]} ∗ ⌜ 1 <= f <= client_fl ⌝) ∨ *)
  (*         ⌜ L = ∅ ⌝ ∗ ⌜ Ract = {[ ρ_cl ]} /\ Rfr = {[ ρ_lib ]} ⌝ ∗ partial_fuel_is {[ inr ρy := client_fl ]}) ∗ *)
  (*       partial_mapping_is {[ 0 := Ract ]} ∗ *)
  (*       partial_free_roles_are Rfr ∗ *)
  (*       y_frag_model_is 1). *)


  Definition relies_on_lib (g_cl: locale heap_lang) 
    (τ: locale heap_lang) (gl: lib_grole): iProp Σ :=
    ⌜ gl = ρlg ⌝ ∗
    τ ⤞_cl g_cl ∗
    own cl_tracker_name (◯E tr_tracked) ∗
    y_frag_model_is 1 ∗    
    ∃ (R__cur R__free: gset (fmrole client_model_impl)), 
      own cl_set_pair_name ((◯ (Excl' (R__cur, R__free))): set_pair_RA) ∗
      partial_mapping_is {[ g_cl := R__cur ]} ∗ 
      partial_fuel_is (gset_to_gmap client_fl R__cur) ∗ 
      partial_free_roles_are R__free. 
  
  (* Notation " τ '⤞_lib' r" := (relies_on_lib τ r) (at level 20). *)

  Definition lib_model_plugged (g_cl: locale heap_lang) ε: iProp Σ :=
    let ron_lib := relies_on_lib g_cl in
    ∀ P Q (gl: lib_grole),
      □ (∀ (δ: fmstate lf), P ∗ model_state_interp δ (fG := cl_lib_Σ) ==∗ 
       ∃ δ', Q ∗ model_state_interp δ' (fG := cl_lib_Σ) ∗ ⌜ fmtrans lf δ (Some gl) δ' ⌝) →
      (∀ (τ: locale heap_lang) (extr: execution_trace heap_lang) (auxtr: auxiliary_trace M) c2,
        (* τ ⤞_lib gl ∗  *) ron_lib τ gl ∗
        P ∗ 
        em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := heap_fairnessGS) ∗
        ⌜ locale_step (trace_last extr) (Some τ) c2 ⌝ 
        ={ ε }=∗
         ∃ (δ2 : M) (ℓ : mlabel M),
         (* τ ⤞_lib gl ∗ *) ron_lib τ gl ∗ 
         Q ∗
         em_msi c2 δ2 (em_GS0 := heap_fairnessGS) ∗
         ⌜em_valid_state_evolution_fairness (extr :tr[ Some τ ]: c2) (auxtr :tr[ ℓ ]: δ2)⌝).

  (* TODO: move*)
  Lemma ite_fun `{Decision P} {A B: Type} (x y: A) (f: A -> B):
    f (if decide P then x else y) = if decide P then f x else f y.
  Proof. destruct decide; done. Qed. 

  (* TODO: move*)
  Lemma ite_fun2 `{Decision P} {A B C: Type} (a1 a2: A) (b1 b2: B) (f: A -> B -> C):
    uncurry f (if decide P then (a1, b1) else (a2, b2)) = if decide P then f a1 b1 else f a2 b2.
  Proof. destruct decide; done. Qed. 

  (* TODO: move*)
  Lemma ite_pair `{Decision P} {A B: Type} (a1 a2: A) (b1 b2: B):
    (if decide P then (a1, b1) else (a2, b2)) =
    (if decide P then a1 else a2, if decide P then b1 else b2).
  Proof. destruct decide; done. Qed. 

  (* TODO: move, generalize? *)
  Lemma gset_to_gmap_singleton `{Countable K} {V: cmra} (v: V) (k: K):
    gset_to_gmap v {[ k ]} ≡  {[ k := v ]}.
  Proof.
    rewrite -gset_to_gmap_singletons. by rewrite big_opS_singleton.
  Qed. 

  Lemma lib_MP g_cl Einvs (DISJ_INV: Einvs ## ↑Ns):
    LSG Einvs ∗ client_inv ⊢
    lib_model_plugged g_cl (Einvs ∪ ↑Ns).
  Proof.
    iIntros "[#PMP #COMP]". 
    rewrite /lib_model_plugged. iIntros "%P %Q %gl #LIB_STEP".
    iIntros "%τ %etr %mtr %c' (RONl & P & MSI_M & %HL_STEP)".
    simpl. 
    

    iInv Ns as ((lb, y)) ">(ST & YST_AUTH & MSI_LIB & TRACK_AUTH)" "CLOS".
    rewrite /relies_on_lib. iDestruct "RONl" as "(-> & RONc & TRACK & YST & SETS)".
    iDestruct "SETS" as (R__cur R__free) "(SETS & MAPc & FUELc & FRc)". 
    iPoseProof (y_model_agree with "YST_AUTH YST") as "->". 
    iDestruct (get_tracked with "[TRACK TRACK_AUTH]") as "TRACK"; [by iFrame| ].
    rewrite /sets_corr. iDestruct "TRACK" as "(TRACK & (%RC & %RF & SETS_AUTH & %VALR) & TRACK_AUTH)".
    iDestruct (own_valid_2 with "SETS_AUTH SETS") as "%EQR".
    apply auth_both_valid_discrete, proj1, Excl_included, leibniz_equiv in EQR.
    inversion EQR. subst R__cur R__free.

    iMod ("LIB_STEP" with "[P MSI_LIB]") as "STEP_LIB"; [by iFrame| ]. 
    iDestruct "STEP_LIB" as (lb') "(Q&MSI_LIB&%STEP_LIB)".
    destruct VALR as [(ENl & -> & ->) | (DISl & -> & ->)].
    2: { destruct DISl. red. eapply fm_live_spec. simpl. eauto. }

    iAssert (has_fuels g_cl {[ρ_lib := client_fl]})%I with "[MAPc FUELc]" as "HFc".
    { iApply has_fuels_equiv. rewrite dom_singleton_L big_sepM_singleton.
      rewrite gset_to_gmap_singleton. iFrame. }
    rewrite difference_union_distr_l_L. rewrite difference_disjoint_L; [| done].
    rewrite difference_diag_L union_empty_r_L.
    iMod (update_client_state with "[$] [$] [$] [$] [$] [$]") as "EM_STEP"; eauto.
    iDestruct "EM_STEP" as (δ2 ℓ) "(STEP_M & MSI_M & RONc & HFc & STc & FRc)". 
    do 2 iExists _. iFrame.
    iApply fupd_frame_l. iSplitR; [done| ].

    iMod (own_update_2 with "SETS_AUTH SETS") as "SETS". 
    { eapply auth_update with (a' := Excl' (if (decide (role_enabled_model (ρlg: fmrole lf) lb')) then ({[ρ_lib]}, {[ρ_cl]}) else ({[ρ_cl]}, {[ρ_lib]}))). 
      apply option_local_update. apply exclusive_local_update.
      done. }
    iDestruct (own_op with "SETS") as "[SETS_AUTH SETS]".

    iDestruct (has_fuels_equiv with "HFc") as "[MAPc FUELc]".
    erewrite ite_fun with (f := dom). rewrite !dom_singleton_L.
    
    do 2 iExists _. iFrame.
    iMod ("CLOS" with "[-SETS FUELc]") as "_".
    2: { iModIntro.
         repeat erewrite <- ite_fun with (f := singleton).
         erewrite <- ite_fun with (f := fun x => singletonM x client_fl).         
         rewrite gset_to_gmap_singleton. rewrite big_sepM_singleton. iFrame.
         rewrite !ite_neg. destruct decide; by iFrame. }
    iNext. iExists (_, _). iFrame.
    rewrite /tracked. iLeft. iFrame. rewrite /sets_corr.
    do 2 iExists _. rewrite ite_pair. iFrame.
    iPureIntro. destruct decide; tauto. 
  Qed. 

  
  
  (* TODO: restore proofs below;
     try to write a universal one covering any allowed lib proof rule *)
  
  (* Lemma lib_open_inv `{clientGS Σ} ζ fs (FSnz : fs ≠ ∅): *)
  (*   client_inv -∗ has_fuels ζ fs (PMPP := lib_PMPP) -∗ *)
  (*   |={↑Ns, ∅}=> *)
  (*   ⌜ ζ = 0 ⌝ ∗ *)
  (*   (∃ lb, partial_model_is (lb, 1) (PartialModelPredicatesPre := PMPP) ∗ model_state_interp lb) ∗ *)
  (*   frag_mapping_is {[ρlg := dom fs]}  ∗ y_auth_model_is 1 ∗ *)
  (*   (∃ f, partial_fuel_is {[ρ_lib := f]} ∗ ⌜ 1 <= f <= client_fl ⌝) ∗ *)
  (*   partial_mapping_is {[0 := {[ρ_lib]}]} ∗ *)
  (*   partial_free_roles_are {[inr ρy]} ∗ y_frag_model_is 1 ∗ *)
  (*   frag_fuel_is fs ∗ *)
  (*   (▷ (∃ st, client_inv_impl st) ={ ∅, ↑Ns}=∗ emp). *)
  (* Proof. *)
  (*   iIntros "#INV FUELS_LIB". *)
  (*   iInv Ns as ((lb, y)) ">(ST & YST_AUTH & inv')" "CLOS". *)
  (*   rewrite difference_diag_L. iModIntro. *)
  (*   iDestruct (has_fuels_equiv with "FUELS_LIB") as "[MAP_LIB FUEL_LIB]". *)
  (*   simpl. iDestruct "MAP_LIB" as (???) "(%LIBM&LM&MATCH&MAP&FR&YST)". *)
  (*   assert (ζ = 0 /\ L = dom fs) as [-> ->]; [| clear LIBM]. *)
  (*   { by apply map_singleton_inj in LIBM as [-> <-]. } *)
  (*   (* assert (S <$> fs ≠ ∅) by (by intros ?%fmap_empty_inv). *) *)
  (*   iDestruct "MATCH" as "[(_&[-> ->]&(%f & Ff & %BOUND)) | [% _]]". *)
  (*   2: { exfalso. apply FSnz. apply dom_empty_iff. set_solver. } *)
  (*   iPoseProof (y_model_agree with "YST_AUTH YST") as "->". *)
  (*   iPoseProof (frag_mapping_same with "[inv'] LM") as "%TMAP0". *)
  (*   { iDestruct "inv'" as (?)"(?&?&?)". iFrame. } *)
  (*   iPoseProof (frag_fuel_included with "[inv'] [FUEL_LIB]") as "%FUEL0". *)
  (*   { iDestruct "inv'" as (?)"(?&?&?&?)". iFrame. } *)
  (*   { iApply frag_fuel_is_big_sepM; [done | by iFrame]. } *)
  (*   iSplitR; [done| ]. *)
  (*   iFrame. iSplitL "ST inv'". *)
  (*   - iExists lb. iFrame.  *)
  (*   - iDestruct (frag_fuel_is_big_sepM with "FUEL_LIB") as "?"; [done| ]. *)
  (*     iFrame. iExists _. iFrame. done. *)
  (* Qed. *)


  (* Lemma fuel_keep_step_lifting `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns): *)
  (* LSG Einvs ∗ client_inv ⊢ *)
  (* ∀ (extr : execution_trace heap_lang) (auxtr : auxiliary_trace M) *)
  (*   (c2 : cfg heap_lang) (fs : gmap (fmrole lib_model_impl) nat) *)
  (*   (ζ : locale heap_lang) (_ : dom fs ≠ ∅) (_ : locale_step *)
  (*                                                  (trace_last extr) *)
  (*                                                  (Some ζ) c2), *)
  (*   has_fuels ζ (S <$> fs) (PMPP := lib_PMPP) -∗ *)
  (*   em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := heap_fairnessGS) *)
  (*   ={Einvs ∪ ↑Ns}=∗ *)
  (*   ∃ (δ2 : M) (ℓ : mlabel M), *)
  (*     ⌜em_valid_state_evolution_fairness (extr :tr[ Some ζ ]: c2) *)
  (*        (auxtr :tr[ ℓ ]: δ2)⌝ ∗ *)
  (*     has_fuels ζ (filter (λ '(k, _), k ∈ dom fs ∖ ∅) fs) (PMPP := lib_PMPP) ∗ *)
  (*     em_msi c2 δ2 (em_GS0 := heap_fairnessGS). *)
  (* Proof. *)
  (*   iIntros "[#PMP #COMP]". iIntros "* FUELS_LIB MSI". simpl in *. *)
    
  (*   assert (S <$> fs ≠ ∅) as NE. *)
  (*   { intros ?%dom_empty_iff. set_solver. } *)

  (*   iPoseProof (lib_open_inv with "[$] FUELS_LIB") as "INV'"; [set_solver| ]. *)
  (*   rewrite union_comm_L. *)
  (*   iMod (fupd_mask_frame_r _ _ Einvs with "INV'") as *)
  (*     "(-> & (%lb & ST & inv') & LM & YST_AUTH & (%f & Ff & %BOUND) & MAP & FR & YST & FUEL_LIB & CLOS)"; [set_solver| ]. *)

    
  (*   iMod (actual_update_no_step_enough_fuel_keep with "[LM FUEL_LIB] inv'") as (lb') "(%LIB_STEP & FUELS_LIB & MSI_LIB & %TMAP_LIB)". *)
  (*   (* 3: { apply empty_subseteq. } *) *)
  (*   { eauto. } *)
  (*   { clear. red. intros. done. } *)
  (*   { rewrite /has_fuels_S. rewrite has_fuels_equiv. iFrame. *)
  (*     iApply frag_fuel_is_big_sepM; done. } *)
    
  (*   destruct (trace_last extr) as (σ1, tp1) eqn:LASTE. destruct c2 as (σ2, tp2). *)
  (*   rewrite LASTE. *)
  (*   rewrite difference_empty_L. *)
  (*   (* rewrite difference_empty_L in TMAP_LIB. *) *)
  (*   iAssert (has_fuels 0 {[ ρ_lib := f ]}) with "[MAP Ff]" as "FUELS". *)
  (*   { rewrite /has_fuels. rewrite dom_singleton_L big_sepS_singleton. *)
  (*     rewrite lookup_singleton. iFrame. iExists _. iFrame. done. } *)

  (*   rewrite -LASTE. *)
  (*   iPoseProof (update_client_state with "[$] [$] [$] [$] [$]") as "EM_STEP"; eauto. *)
  (*   { eexists. split; [apply LIB_STEP| ]. done. } *)
  (*   { lia. } *)
  (*   iMod (fupd_mask_mono with "EM_STEP") as (δ2 ℓ) "(EV & MSI & FUELS & ST & FR)"; [set_solver| ]. *)
  (*   do 2 iExists _. iFrame "EV MSI". *)
  (*   rewrite gmap_filter_dom_id.  *)

  (*   iDestruct ("CLOS" with "[ST MSI_LIB YST_AUTH]") as "CLOS". *)
  (*   { iNext. iExists (_, _). rewrite /client_inv_impl. iFrame. } *)
  (*   iMod (fupd_mask_frame_r _ _ Einvs with "CLOS") as "_"; [set_solver| ]. *)

  (*   iModIntro. *)
  (*   iDestruct "FUELS" as "[MAP FUEL]". iDestruct "FUELS_LIB" as "[MAP_LIB FUELS_LIB]". *)
  (*   rewrite /has_fuels. iSplitR "FUELS_LIB". *)
  (*   2: { done. } *)
  (*   simpl.  *)
  (*   rewrite /lib_pmi. do 3 iExists _. iFrame. *)
  (*   iSplitR; [done| ]. *)
  (*   (* TODO: case when domain becomes empty *) *)
  (*   iLeft. iSplitR; [done| ]. *)
  (*   rewrite TMAP_LIB. *)
  (*   (* rewrite lookup_insert. *) *)

  (*   assert (ls_tmap lb !! ρlg ≠ Some ∅) as TM_NE. *)
  (*   { edestruct (locale_trans_ex_role lb ρlg lb' (LM := lib_model lib_gs)) as [? STEP]. *)
  (*     { eexists. split; [apply LIB_STEP| ]. done. } *)
  (*   eapply ls_mapping_tmap_corr in STEP as (?&?&?). rewrite H1. set_solver. }  *)
    
  (*   repeat erewrite @decide_False; try done.  *)
  (*   iSplitR. *)
  (*   - iPureIntro.  set_solver. *)
  (*   - rewrite dom_singleton_L big_sepS_singleton. *)
  (*     rewrite lookup_singleton. *)
  (*     iDestruct "FUEL" as (?) "[%EQ ?]". inversion EQ. subst. *)
  (*     iExists _. iFrame. iPureIntro. lia. *)
  (* Qed. *)

  (* Lemma lib_fuel_drop_step_preserves_LSI s rem: *)
  (*   fuel_drop_preserves_LSI s rem (LSI := LSI_groups_fixed lib_gs (M := lib_model_impl)). *)
  (* Proof.  *)
  (*   (* done. *) *)
  (*   red. intros. red. rewrite dom_fmap. apply H0.  *)
  (* Qed.  *)
    

  (* Lemma fuel_drop_step_lifting `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns): *)
  (* LSG Einvs ∗ client_inv ⊢ *)
  (* ∀ (extr : execution_trace heap_lang) (auxtr : auxiliary_trace M) *)
  (*   (c2 : cfg heap_lang) s (fs : gmap (fmrole lib_model_impl) nat) *)
  (*   rem *)
  (*   (ζ : locale heap_lang) (_ : dom fs ≠ ∅) *)

  (*   (_: (live_roles _ s) ∩ rem = ∅) *)
  (*   (_: rem ⊆ dom fs) *)
  (*   (_ : locale_step (trace_last extr) (Some ζ) c2), *)
  (*   has_fuels ζ (S <$> fs) (PMPP := lib_PMPP) -∗ *)
  (*   partial_model_is s -∗ *)
  (*   em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := heap_fairnessGS) *)
  (*   ={Einvs ∪ ↑Ns}=∗ *)
  (*   ∃ (δ2 : M) (ℓ : mlabel M), *)
  (*     ⌜em_valid_state_evolution_fairness (extr :tr[ Some ζ ]: c2) *)
  (*        (auxtr :tr[ ℓ ]: δ2)⌝ ∗ *)
  (*     has_fuels ζ (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs) (PMPP := lib_PMPP) ∗ *)
  (*     partial_model_is s ∗ *)
  (*     em_msi c2 δ2 (em_GS0 := heap_fairnessGS). *)
  (* Proof. *)
  (*   iIntros "[#PMP #COMP]". iIntros "* FUELS_LIB ST_LIB MSI". simpl in *. *)
    
  (*   assert (S <$> fs ≠ ∅) as NE. *)
  (*   { intros ?%dom_empty_iff. set_solver. } *)

  (*   iPoseProof (lib_open_inv with "[$] FUELS_LIB") as "INV'"; [set_solver| ]. *)
  (*   rewrite union_comm_L. *)
  (*   iMod (fupd_mask_frame_r _ _ Einvs with "INV'") as *)
  (*     "(-> & (%lb & ST & inv') & LM & YST_AUTH & (%f & Ff & %BOUND) & MAP & FR & YST & FUEL_LIB & CLOS)"; [set_solver| ]. *)

  (*   iAssert (⌜ s = ls_under lb ⌝)%I as %->. *)
  (*   { rewrite /model_state_interp. *)
  (*     iDestruct "inv'" as (?)"(?&?&?&ST_LIB'&?)". *)
  (*     (* TODO: make a lemma? *) *)
  (*     by iDestruct (own_valid_2 with "ST_LIB' ST_LIB") as *)
  (*     %[Heq%Excl_included%leibniz_equiv ?]%auth_both_valid_discrete. } *)
      
      
  (*   iMod (actual_update_no_step_enough_fuel_drop with "[LM FUEL_LIB] ST_LIB inv'") as (lb') "(%LIB_STEP & FUELS_LIB & ST_LIB & MSI_LIB & %TMAP_LIB)". *)
  (*   (* 3: { apply empty_subseteq. } *) *)
  (*   { eauto. } *)
  (*   4: { rewrite /has_fuels_S. rewrite has_fuels_equiv. iFrame. *)
  (*        iApply frag_fuel_is_big_sepM; done. } *)
  (*   2: { eauto. } *)
  (*   { done. } *)
  (*   { apply lib_fuel_drop_step_preserves_LSI. } *)
    
  (*   destruct (trace_last extr) as (σ1, tp1) eqn:LASTE. destruct c2 as (σ2, tp2). *)
  (*   rewrite LASTE. *)
  (*   (* rewrite difference_empty_L. *) *)
  (*   (* rewrite difference_empty_L in TMAP_LIB. *) *)
  (*   iAssert (has_fuels 0 {[ ρ_lib := f ]}) with "[MAP Ff]" as "FUELS". *)
  (*   { rewrite /has_fuels. rewrite dom_singleton_L big_sepS_singleton. *)
  (*     rewrite lookup_singleton. iFrame. iExists _. iFrame. done. } *)

  (*   rewrite -LASTE. *)
  (*   iPoseProof (update_client_state with "[$] [$] [$] [$] [$]") as "EM_STEP"; eauto. *)
  (*   { eexists. split; [apply LIB_STEP| ]. done. } *)
  (*   { lia. } *)
  (*   iMod (fupd_mask_mono with "EM_STEP") as (δ2 ℓ) "(EV & MSI & FUELS & ST & FR)"; [set_solver| ]. *)
  (*   do 2 iExists _. iFrame "EV MSI". *)

  (*   iDestruct ("CLOS" with "[ST MSI_LIB YST_AUTH]") as "CLOS". *)
  (*   { iNext. iExists (_, _). rewrite /client_inv_impl. iFrame. } *)
  (*   iMod (fupd_mask_frame_r _ _ Einvs with "CLOS") as "_"; [set_solver| ]. *)

  (*   iModIntro. *)
  (*   iDestruct "FUELS" as "[MAP FUEL]". iDestruct "FUELS_LIB" as "[MAP_LIB FUELS_LIB]". *)

  (*   iFrame "ST_LIB".  *)
  (*   iSplitR "FUELS_LIB". *)
  (*   2: { rewrite dom_domain_restrict; [| set_solver]. done. } *)
  (*   simpl. rewrite dom_domain_restrict; [| set_solver]. *)
  (*   rewrite /lib_pmi. do 3 iExists _. iFrame. *)
  (*   iSplitR; [done| ]. *)

  (*   rewrite TMAP_LIB. rewrite lookup_insert. *)
  (*   destruct (decide (dom fs = rem)). *)
  (*   2: {  *)

  (*   iLeft. *)
  (*   iSplitR. *)
  (*   { iPureIntro. intros ?. apply n. set_solver. }  *)
  (*   (* rewrite lookup_insert. *) *)
  (*   repeat erewrite @decide_False with (P := (Some (dom fs ∖ rem) = Some ∅)). *)
  (*   (* 2-3: by intros [=]. *) *)
  (*   2, 3: intros [=]; set_solver.  *)
  (*   iSplitR. *)
  (*   { iPureIntro. set_solver. } *)
  (*   rewrite dom_singleton_L big_sepS_singleton. *)
  (*   rewrite lookup_singleton. *)
  (*   iDestruct "FUEL" as (?) "[%EQ ?]". inversion EQ. subst. *)
  (*   iExists _. iFrame. iPureIntro. lia. } *)
    
  (*   subst rem. iRight. iSplitR. *)
  (*   { iPureIntro. set_solver. } *)
  (*   rewrite difference_diag_L. repeat erewrite decide_True. *)
  (*   2, 3: done. *)
  (*   iSplitR. *)
  (*   { iPureIntro. set_solver. } *)
  (*   rewrite dom_singleton_L big_sepS_singleton. *)
  (*   rewrite lookup_singleton. *)
  (*   iDestruct "FUEL" as (?) "[%EQ ?]". inversion EQ. *)
  (*   iFrame.          *)
  (* Qed. *)


  (* Lemma lib_model_step_preserves_LSI: *)
  (* ∀ (s1 : lib_model_impl) (ρ : fmrole lib_model_impl)  *)
  (*   (s2 : lib_model_impl) (fs1 fs2 : gmap (fmrole lib_model_impl) nat), *)
  (*   model_step_preserves_LSI s1 ρ s2 fs1 fs2 (LSI := LSI_groups_fixed lib_gs). *)
  (* Proof. *)
  (*   (* can be proven trivially, but the proof below should work for non-trivial Gs *) *)
  (*   intros. red. intros * LSI1 STEP INρ. red. intros g' DOMg'. *)
  (*   apply LSI1. *)
  (*   rewrite dom_insert_L in DOMg'. *)
  (*   apply elem_of_union in DOMg' as [IN| ?]; [| done]. *)
  (*   apply elem_of_singleton in IN as ->. *)
  (*   eapply @elem_of_dom; [by apply _| ]. *)
  (*   destruct (R !! g) eqn:RG; done.  *)
  (* Qed. *)
    
  (* Lemma model_step_lifting `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns): *)
  (* LSG Einvs ∗ client_inv ⊢ *)
  (* ∀ (extr : execution_trace heap_lang) (auxtr : auxiliary_trace M) *)
  (*   (tp1 tp2 : list (language.expr heap_lang)) (σ1 σ2 : language.state heap_lang) *)
  (*   (s1 s2 : lib_model_impl) (fs1 fs2 : gmap (fmrole lib_model_impl) nat) *)
  (*   (ρ : fmrole lib_model_impl) (δ1 : M) (ζ : locale heap_lang) *)
  (*   (fr1 fr_stash : gset (fmrole lib_model_impl)) *)
  (*   (_ : live_roles lib_model_impl s2 ∖ live_roles lib_model_impl s1 ⊆ fr1 ∪ dom fs1 ∩ dom fs2) *)
  (*   (_ : fr_stash ⊆ dom fs1) (_ : live_roles lib_model_impl s1 *)
  (*                                 ∩ (fr_stash ∖ {[ρ]}) = ∅) *)
  (*   (_ : dom fs2 ∩ fr_stash = ∅) (_ : trace_last extr = (tp1, σ1)) *)
  (*   (_ : trace_last auxtr = δ1) (_ : locale_step (tp1, σ1) (Some ζ) (tp2, σ2)) *)
  (*   (_ : fmtrans lib_model_impl s1 (Some ρ) s2) *)
  (*   (_ : valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := lib_model lib_gs)) *)
  (* , *)
  (*   has_fuels ζ fs1 (PMPP := lib_PMPP) -∗ *)
  (*   partial_model_is s1 (PartialModelPredicatesPre := lib_PMPP) -∗ *)
  (*   em_msi (tp1, σ1) δ1 (em_GS0 := heap_fairnessGS) -∗ *)
  (*   partial_free_roles_are fr1 (PartialModelPredicatesPre := lib_PMPP) *)
  (*   ={Einvs ∪ ↑Ns}=∗ *)
  (*   ∃ (δ2 : M) (ℓ : mlabel M), *)
  (*     ⌜em_valid_state_evolution_fairness (extr :tr[ Some ζ ]: (tp2, σ2)) *)
  (*        (auxtr :tr[ ℓ ]: δ2)⌝ ∗ *)
  (*     has_fuels ζ fs2 (PMPP := lib_PMPP) ∗ *)
  (*     partial_model_is s2 (PartialModelPredicatesPre := lib_PMPP) ∗ *)
  (*     em_msi (tp2, σ2) δ2 (em_GS0 := heap_fairnessGS) ∗ *)
  (*     partial_free_roles_are *)
  (*       (fr1 ∖ (live_roles lib_model_impl s2 ∖ (live_roles lib_model_impl s1 ∪ dom fs1 ∩ dom fs2)) *)
  (*        ∪ fr_stash) (PartialModelPredicatesPre := lib_PMPP). *)
  (* Proof. *)
  (*   iIntros "[#PMP #COMP]". iIntros "* FUELS_LIB ST_LIB MSI FR_LIB". simpl in *. *)
    
  (*   assert (ρ ∈ dom fs1) as DOM1ρ by apply x7. *)
  (*   assert (dom fs1 ≠ ∅ /\ fs1 ≠ ∅) as [FS1nz FS1nz']. *)
  (*   { split; intros ?; set_solver. } *)
    
  (*   iPoseProof (lib_open_inv with "[$] FUELS_LIB") as "INV'"; [done| ]. *)
  (*   rewrite union_comm_L. *)
  (*   iMod (fupd_mask_frame_r _ _ Einvs with "INV'") as *)
  (*     "(-> & (%lb & ST & inv') & LM & YST_AUTH & (%f & Ff & %BOUND) & MAP & FR & YST & FUEL_LIB & CLOS)"; [set_solver| ]. *)

  (*   iPoseProof (LM_steps_gen_nofork_sub with "PMP") as "PMP'". *)
  (*   iMod (actual_update_step_still_alive_gen with "[LM FUEL_LIB] [$] [$] [$]") as "LIFT"; eauto. *)
  (*   2: { rewrite has_fuels_equiv. iFrame. iApply frag_fuel_is_big_sepM; done. } *)
  (*   { apply lib_model_step_preserves_LSI. } *)

  (*   iDestruct "LIFT" as (lb') "(%LIB_STEP & FUELS_LIB & ST_LIB & MSI_LIB & FR_LIB & %TMAP_LIB)". *)
  (*   simpl. iFrame "ST_LIB". *)
    
  (*   iAssert (has_fuels 0 {[ ρ_lib := f ]}) with "[MAP Ff]" as "FUELS". *)
  (*   { rewrite /has_fuels. rewrite dom_singleton_L big_sepS_singleton. *)
  (*     rewrite lookup_singleton. iFrame. iExists _. iFrame. done. } *)

  (*   rewrite -x3 -x4. rewrite -x3 in x5. *)
  (*   iPoseProof (update_client_state with "[$] [MSI] [ST] [$] [$]") as "EM_STEP"; eauto. *)
  (*   { eexists. split; [apply LIB_STEP| ]. done. } *)
  (*   { lia. } *)
  (*   iMod (fupd_mask_mono with "EM_STEP") as (δ2 ℓ) "(EV & MSI & FUELS & ST & FR)"; [set_solver| ]. *)
  (*   do 2 iExists _. iFrame "EV MSI". *)

  (*   iDestruct ("CLOS" with "[ST MSI_LIB YST_AUTH]") as "CLOS". *)
  (*   { iNext. iExists (_, _). rewrite /client_inv_impl. iFrame. } *)
  (*   iMod (fupd_mask_frame_r _ _ Einvs with "CLOS") as "_"; [set_solver| ]. *)
  (*   iModIntro. *)

  (*   rewrite !has_fuels_equiv. simpl. *)
  (*   iDestruct "FUELS" as "[MAP FUELS]". *)
  (*   iDestruct "FUELS_LIB" as "[MAP' FUELS_LIB]". iFrame "FUELS_LIB FR_LIB". *)
  (*   rewrite /lib_pmi. do 3 iExists _. iFrame. *)
  (*   iSplitR; [done |]. *)
  (*   rewrite TMAP_LIB. rewrite lookup_insert. *)
  (*   dEq. *)
  (*   - iRight. rewrite big_sepM_singleton. iFrame. *)
  (*     iPureIntro. set_solver. *)
  (*   - iLeft. rewrite big_sepM_singleton. *)
  (*     iApply bi.sep_assoc. iSplitR "FUELS". *)
  (*     2: { iExists _. iFrame. iPureIntro. lia. } *)
  (*     iPureIntro. split; [| set_solver]. intros ?. rewrite H1 in n. done. *)
  (* Qed. *)


  Lemma lib_PMP `{clientGS Σ} Einvs (DISJ_INV: Einvs ## ↑Ns):
    LSG Einvs ∗ client_inv ⊢
    (* PartialModelPredicates (Einvs ∪ ↑Ns) (LM := LM) (iLM := spinlock_model) (PMPP := (sl1_PMPP γ)).  *)
    LM_steps_gen_nofork (Einvs ∪ ↑Ns) (EM := EM) (iLM := lib_model lib_gs) (PMPP := lib_PMPP) (eGS := heap_fairnessGS) (relies_on := relies_on_lib).
  Proof.
    (* iIntros "[#PMP #COMP]". iApply @Build_LM_steps_gen_nofork. *)

    (* iModIntro. repeat iSplitR. *)
    (* - iIntros "* FUELS_LIB ST MSI". *)
    (*   iDestruct (fuel_drop_step_lifting with "[$] [] [] [] [] FUELS_LIB ST MSI") as "LIFT"; eauto. *)
    (*   (* change the PMP interface so it allows fupd in fuel step *) *)
    (*   admit.       *)
    (* - iIntros "* FUELS_LIB MSI". *)
    (*   iDestruct (fuel_keep_step_lifting with "[$] [] [] FUELS_LIB MSI") as "LIFT"; eauto. *)
    (*   (* same as above *) *)
    (*   admit. *)
    (* - iIntros "* FUELS_LIB ST MSI FR". *)
    (*   iApply (model_step_lifting with "[$] [] [] [] [] [] [] [] [] [] [$] [$] [$] [$]"); eauto. *)

  Admitted.

End LibPMP. 
