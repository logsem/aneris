From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness.heap_lang Require Export lang lm_lsi_hl_wp tactics proofmode_lsi.
From trillium.fairness Require Import lm_fair fuel_ext fairness_finiteness. 
From trillium.fairness.heap_lang Require Import notation wp_tacs.

Close Scope Z_scope.

Section LibraryDefs.

  Definition lib_model_impl: FairModel.
    refine ({|
        fmstate := nat;
        fmrole := unit;
        fmtrans s1 oρ s2 := s1 = 1 /\ s2 = 0;
        live_roles s := if (decide (s = 1)) then {[ tt ]} else ∅;
        (* fuel_limit _ := 25%nat; (* exact value; should relax its usage *) *)
             |}).
    intros. set_solver. 
  Defined. 

  (* simply to differentiate between group- and individual role *)
  Definition lib_grole := unit.
  Definition ρlg: lib_grole := tt. 

  Definition ρl: fmrole lib_model_impl := tt.

  Definition LSI_groups_fixed (gs: gset lib_grole):
    fmstate lib_model_impl → groups_map (M := lib_model_impl) → fuel_map (M := lib_model_impl) → Prop := 
    fun _ tm _ => dom tm ⊆ gs.

  Global Instance LSI_gf_dec gs:
    forall s tm fm, Decision (LSI_groups_fixed gs s tm fm).
  Proof.
    intros. rewrite /LSI_groups_fixed. solve_decision.
  Qed. 

  Definition lib_fl := 5.
  Definition lib_model gs: LiveModel lib_grole lib_model_impl (LSI_groups_fixed gs) := 
    {| lm_fl _ := lib_fl; |}.

  (* Definition lib_lm_LSI_alt gs (δ: lm_ls (lib_model gs)): *)
  (*   dom (ls_tmap δ) ⊆ gs. *)
  (* Proof.  *)
  (*   apply elem_of_subseteq. intros g.  *)
  
  Definition lib_fun: val :=
    λ: <>,
      let: "y" := ref #1 in
      "y" <- #0. 

  Lemma lib_model_impl_lr_strong: FM_strong_lr lib_model_impl.
  Proof. 
    red. intros. simpl.
    destruct st; [| destruct st]; set_solver. 
  Qed. 

  (* TODO: this is needed to prove lib termination; should extract this part *)
  From trillium.fairness Require Import fair_termination trace_helpers trace_lookup. 

  (* straightforward proof which can be done more idiomatically 
     by providing FairTerminatingModel of library *)
  Lemma lib_fair_term:
    ∀ mtr: mtrace lib_model_impl, mtrace_fairly_terminating mtr. 
  Proof.
    red. intros mtr VALID FAIR. 
    destruct mtr; [by exists 1| ].
    destruct mtr; [by exists 2| ].
    pose proof (trace_valid_steps' _ _ VALID 0) as STEP0.
    pose proof (trace_valid_steps' _ _ VALID 1) as STEP1.
    rewrite trace_lookup_0_cons in STEP0. simpl in STEP0. 
    specialize (STEP0 _ _ _ eq_refl) as [-> ->].
    rewrite trace_lookup_cons trace_lookup_0_cons in STEP1.
    specialize (STEP1 _ _ _ eq_refl). by inversion STEP1.
  Qed.


  (* TODO: generalize to any LSI_True model *)
  Instance lib_model_inh gs (NE: gs ≠ ∅): Inhabited (lm_ls (lib_model gs)).
  Proof. 
    (* pose proof (fmrole_inhabited lib_model_impl) as [ρ]. *)
    (* pose proof (fmstate_inhabited lib_model_impl) as [s]. *)
    apply finitary.set_choose_L' in NE as [g GS]. 
    pose proof (fmstate_inhabited lib_model_impl) as [s].
    eapply populate, (initial_ls' s g).
    red. simpl. red. rewrite dom_singleton. set_solver. 
  Qed.


  Instance lib_lm_dec_ex_step gs:
  ∀ (τ : lib_grole) (δ1 : lm_ls (lib_model gs)),
    Decision (∃ δ2, locale_trans δ1 τ δ2).
  Proof. 
    intros.
    apply locale_trans_ex_dec_fin with (steps := [0]).
    - intros. inversion H. set_solver.
    - intros. eexists. eapply rearrange_roles_spec.
      Unshelve.
      + exact (lib_model gs).
      + red. intros ?. 
        rewrite /rearrange_roles_map. rewrite dom_insert.
        intros [->%elem_of_singleton | IN]%elem_of_union; apply (ls_inv δ0).
        { eapply locale_trans_dom; eauto. }
        by apply dom_filter_sub in IN. 
  Defined.

  Global Instance lib_LF gs (NE: gs ≠ ∅): LMFairPre (lib_model gs).
    esplit; try by apply _.
    by apply lib_model_inh. 
  Defined.
  
  (* Definition lib_fair gs (NE: gs ≠ ∅) := LM_Fair (LM := (lib_model gs)).  *)
  Definition lib_fair gs (NE: gs ≠ ∅) :=
    @LM_Fair _ _ _ _ _ _ (lib_LF gs NE).

End LibraryDefs.

Global Opaque lib_model_impl. 
Global Opaque lib_grole ρlg. 

Section LibrarySpec.
  Context `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM}.
  Context `{PMPP: @PartialModelPredicatesPre (locale heap_lang) _ _ Σ lib_model_impl}.
  (* Context {ifG: fairnessGS lib_model Σ}. *)
  
  Notation "'PMP' gs" := (fun Einvs => (LM_steps_gen_nofork Einvs (EM := EM) (iLM := lib_model gs) (PMPP := PMPP) (eGS := heap_fairnessGS))) (at level 10). 

  Lemma lib_LSI_fuel_independent gs:
    LSI_fuel_independent (LSI := LSI_groups_fixed gs).
  Proof.
    red. rewrite /LSI_groups_fixed. intros.
    eapply H0; eauto. 
  Qed.

  Lemma lib_spec tid gs Einvs f (F2: f >= 4):
    PMP gs Einvs -∗
    {{{ partial_model_is 1 (PartialModelPredicatesPre := PMPP) ∗ 
        has_fuels tid {[ ρl:=f ]} (PMPP := PMPP)  }}}
      lib_fun #() @ tid
    {{{ RET #(); partial_mapping_is {[ tid := ∅ ]} ∗ 
                 partial_free_roles_are {[ ρl ]} }}}.
  Proof using.
    iIntros "#PMP" (Φ) "!> (ST & FUELS) POST". rewrite /lib_fun.

    rewrite (sub_0_id {[ _ := _ ]}).
    assert (fuels_ge ({[ρl := f]}: gmap (fmrole lib_model_impl) nat) 4) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }

    pure_step FS lib_LSI_fuel_independent.

    wp_bind (ref _)%E.
    iApply (wp_alloc_nostep with "[$] [FUELS]").
    { apply lib_LSI_fuel_independent. }
    2: { solve_fuels_S FS. }
    { solve_map_not_empty. }
    iNext. iIntros (l) "(L & _ & FUELS) /=".

    do 2 pure_step FS lib_LSI_fuel_independent.

    iApply (wp_store_step_singlerole with "[$] [L ST FUELS]").
    6: { iFrame "L ST". iNext.
         iApply has_fuel_fuels. rewrite map_fmap_singleton. iFrame. }
    { done. }
    2: { econstructor; eauto. }
    { reflexivity. }
    { done. }
    { erewrite decide_False; [| done].
      red. intros. red.
      (* intros ρ g'. *)
      apply elem_of_subseteq. intros g'.
      eintros [Rg' TMg']%@elem_of_dom.
      2: { apply _. }  (* TODO: ? *)
      destruct (R !! g) eqn:EQRg.
      2: { done. }
      simpl in H2. 
      rewrite lookup_insert_Some in TMg'. destruct TMg' as [[<- <-] | [NEQ TMg']].
      { apply H0. eapply @elem_of_dom; [by apply _| ]. eauto. } 
      apply H0. eapply @elem_of_dom; [by apply _| ]. eauto. }
    iNext. iIntros "(L & ST & FUELS)".
    erewrite decide_False; [| done].
    iApply ("POST" with "FUELS"). 
  Qed. 

End LibrarySpec.


Definition lib_ls_premise gs (lb: lm_ls (lib_model gs)) :=
  ls_fuel lb !! ρl = Some (lm_fl (lib_model gs) (ls_under lb)) ∧ ls_under lb = 1 ∧ ls_tmap lb !! ρlg = Some {[ρl]}.

Lemma lib_premise_dis gs (lb: lm_ls (lib_model gs))
  (NE: gs ≠ ∅)
  (LB_INFO: lib_ls_premise gs lb):
  ρlg ∈ live_roles (lib_fair _ NE) lb.
Proof.
  apply LM_live_roles_strong.
  destruct LB_INFO as (F & S & TM).
  unshelve eset (δ := ({| ls_under := (0: fmstate lib_model_impl);
                ls_fuel := ls_fuel lb;
                ls_tmap := ls_tmap lb; ls_inv := _ |})).
  all: try by apply lb. 
  { exact (LSI_groups_fixed gs). }
  { set_solver. } 
  { apply (ls_inv lb). }
  exists δ. red. exists (Take_step ρl ρlg). split; [| done].
  repeat split; eauto.  
  - eapply ls_mapping_tmap_corr. eexists. split; eauto. set_solver.
  - red. intros. inversion H1; subst; try set_solver.
    destruct ρ', ρl; done.
  - red. intros. left.
    replace ρ' with ρl by (by destruct ρ', ρl).
    rewrite F. simpl. lia.
  - intros. rewrite F. simpl. lia.
  - intros. subst δ. simpl in H. set_solver.
  - subst δ. simpl. set_solver.
Qed. 
