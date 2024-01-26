From trillium.fairness.heap_lang Require Import notation simulation_adequacy_lm heap_lang_defs em_lm_heap_lang.
From trillium.fairness Require Import fairness fuel fairness_finiteness lm_fair comp_utils fair_termination lm_fairness_preservation lm_fairness_preservation_wip lm_fair_traces.
From trillium.fairness.ext_models Require Import ext_models.
From trillium.fairness.examples.ticketlock Require Import ticketlock_model_lm client_model ticketlock_model fair_lock lm_restr client_trace_termination fair_lock_lm. 

Section Adequacy.
  Let M := tl_fair_model.
  Let R := fmrole M.
  Let G := @SG M. 
  Let gs2: gset G := @tl_gs 2.

  Let TlLM2 := @tl_model 2.

  Local Instance TlLM2_LF: LMFairPre TlLM2.
  apply _. 
  Defined.

  Lemma TlLM2_LGF st (tm : groups_map) (fm : fuel_map)
    (LSI: @LSI_Tl 2 st tm fm): 
    LSI_groups_fixed gs2 st tm fm.
  Proof.
    red in LSI. do 2 apply proj2 in LSI.
    red. rewrite LSI. set_solver.
  Qed.

  Lemma TlLM2_nexts: forall δ, @next_states (LM_Fair (LF := TlLM2_LF)) δ.
  Proof. 
    unshelve eapply LM_step_fin.
    - apply tl_model_impl_step_fin.
    - exact gs2.
    - intros * (?&?&FIX). subst gs2.
      red. by rewrite FIX.
  Qed.

  Let PKE := @PROJ_KEEP_EXT _ _ _ TLFairLock _ _ TlLM2_LF _
               tl_ls_map_restr tl_unused_not_dom tl_egs.

  Instance Tl2_FLS: FLSubmodel.
  esplit.
  - apply tl_gs_size.
  - apply TlLM2_LGF.
  - apply TlLM2_nexts.
  - apply Tl_FL_LM.
  - apply PKE.
  Qed. 

  Let cmft_instance := @client_model_fair_term Tl2_FLS.

  (* TODO: move to program proof file *)
  Section tmp.

    Class clientPreGS (Σ: gFunctors) := ClientPreGS {
    }.

    Class clientGS Σ := ClientGS {
      cl_pre_inG :> clientPreGS Σ;
    }.

    Definition clientPreΣ : gFunctors :=
      #[].
    
    Global Instance subG_clientPreΣ {Σ}:
      subG clientPreΣ Σ → clientPreGS Σ.
    Qed. 

    Definition client: val.
    Admitted. 

  End tmp.

  (* TODO: adapt proof in comp/lib_ext.v *)
  Lemma lib_keeps_asg: ∀ (δ1 : fmstate LM_Fair) (ι : env_role) (δ2 : fmstate LM_Fair) (ρ: fmrole tl_fair_model) (τ: G) (f : nat),
     @ext_trans _ (FL_EM tl_FLE) δ1 (Some (inr ι)) δ2
     → ls_mapping δ1 !! ρ = Some τ
       → ls_fuel δ1 !! ρ = Some f
         → ls_mapping δ2 !! ρ = Some τ ∧ ls_fuel δ2 !! ρ = Some f.
  Proof.
  Admitted. 

  Lemma client_LM_inner_exposed (auxtr: lmftrace (LM := client_model)):
    inner_obls_exposed (option_fmap _ _ inl) (λ c δ_lib, c.1 = δ_lib) auxtr (LMo := client_model) (AMi := ELM_ALM lib_keeps_asg).
    (*   inner_obls_exposed ((option_fmap _ _ inl) ext_role (ext_role + cl_id)%type inl) *)
    (* (λ (st : client_model_impl) (tl_st : lm_ls TlLM), st.1 = tl_st) auxtr.  *)

  Proof.
    red. simpl. intros n δ gl NTH (?&?&?&MAP).
    eexists. split; [reflexivity| ].
    rewrite (ls_same_doms δ) mapped_roles_dom_fuels.
    apply (ls_inv δ). rewrite H. eauto.
  Qed.

(* TODO: move, generalize *)
Theorem simulation_adequacy_terminate_client (Σ: gFunctors)
        {hPre: @heapGpreS Σ (fair_model_model (@LM_Fair _ _ _ _ _ _ client_LF)) (@LM_EM_HL _ _ client_model client_LF)} (s: stuckness)
        e1 (s1: fmstate client_model_impl) FR
        (LSI0: initial_ls_LSI s1 0 (M := client_model_impl) (LM := client_model) (LSI := client_LSI))
        (INIT: is_init_cl_state s1)
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  rel_finitary (sim_rel client_model (LF := client_LF)) →
  wp_premise (λ _ _, True) (trfirst extr).2 e1 s1 s FR LSI0 ->
  extrace_fairly_terminating extr.
Proof.
  intros Hfb Hwp Hvex Hfair.

  destruct (simulation_adequacy_model_trace
              Σ _ e1 s1 FR LSI0 extr Hvex Hexfirst Hfb Hwp) as (auxtr&mtr&Hmatch&Hupto&A0).

  (* TODO: clarify which types of fairness we need in this proof *)
  assert (forall ρ, fair_aux_SoU (LM_ALM client_model) ρ auxtr (LM := client_model)) as FAIR_SOU.
  { apply group_fairness_implies_step_or_unassign; eauto.
    { eapply traces_match_valid2; eauto. }
    eapply fairness_preserved; eauto.
    { apply _. }
    { intros. apply match_locale_enabled_states_livetids. }
    intros.
    destruct ζ.
    { apply Hfair. }
    simpl. red. simpl in *. by intros ?(?&?&?)%pred_at_trace_lookup. }

  pose proof (ex_fairness_preserved _ _ Hmatch Hfair) as Hfairaux'.
  pose proof (proj1 (LM_ALM_afair_by_next _ auxtr) Hfairaux') as Hfairaux.  
  
  have Hfairm := lm_fair_traces.upto_stutter_fairness auxtr mtr Hupto Hfairaux.
  pose proof (traces_match_valid2 _ _ _ _ _ _ Hmatch) as Hvalaux. 
  have Hmtrvalid := lm_fair_traces.upto_preserves_validity auxtr mtr Hupto Hvalaux.

  assert (mtrace_fairly_terminating mtr) as FAIR_TERM. 
  { eapply client_model_fair_term.
    2: { apply upto_stutter_trfirst in Hupto.
         rewrite Hupto A0. simpl. done. } 
    red. eexists. split; [| split]; eauto.
    by apply client_LM_inner_exposed. }
  assert (terminating_trace mtr) as Hterm.
  { eapply FAIR_TERM; eauto. }
    
  eapply traces_match_preserves_termination =>//.
  eapply lm_fair_traces.upto_stutter_finiteness =>//.
Qed.

  Definition δ0: fmstate TlLM_FM.
  Admitted. 

  Definition st0: fmstate client_model_impl := (δ0, fs_U).

  Lemma st0_lsi: initial_ls_LSI st0 0 (LM := client_model).
  Proof. Admitted. 

  Theorem client_terminates
    (extr : heap_lang_extrace)
    (Hvex : extrace_valid extr)
    (Hexfirst : (trfirst extr).1 = [client #()]):
    (∀ tid, fair_ex tid extr) -> terminating_trace extr.
  Proof.
    set (Σ := gFunctors.app (heapΣ (@LM_EM_HL _ _ client_model client_LF)) clientPreΣ).
    assert (heapGpreS Σ (@LM_EM_HL _ _ client_model client_LF)) as HPreG.
    { apply _. }
    
    eapply (simulation_adequacy_terminate_client Σ NotStuck _ (st0: fmstate client_model_impl) _ LSI0); try done.
    - eapply valid_state_evolution_finitary_fairness_simple.
      apply client_model_finitary.
    - intros ?. iStartProof.
      rewrite /LM_init_resource. iIntros "!> (Hm & FR & Hf) !>".
      iSplitL.
      2: { (* TODO: make a lemma, move it to simulation_adequacy_lm *)
        iIntros (?). iIntros "**".
        iApply (fupd_mask_weaken ∅); first set_solver. by iIntros "_ !>". }
      
      simpl.
      iApply (client_spec ∅ δ_lib0 with "[] [Hm Hf FR]"); eauto.
      { set_solver. }
      { apply init_lib_state. }
      { iApply lm_lsi_toplevel. }
      iFrame.
      iSplitL "FR".
      + simpl. rewrite dom_gset_to_gmap. rewrite difference_twice_L.
        rewrite difference_disjoint; [by iFrame| ].
        subst st0. erewrite live_roles_3. set_solver.
      + subst st0.
        iApply has_fuels_proper; [reflexivity| | by iFrame].
        pose proof (live_roles_3 δ_lib0). simpl in H.
        replace (client_lr (δ_lib0, 3)) with ({[inr ρy]}: gset (fmrole client_model_impl)).
        2: { symmetry. apply leibniz_equiv. apply live_roles_3. }
        rewrite -gset_to_gmap_singletons big_opS_singleton. done.
  Qed.

End Adequacy.
