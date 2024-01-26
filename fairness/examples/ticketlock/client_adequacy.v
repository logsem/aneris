From trillium.fairness Require Import fairness fuel fairness_finiteness lm_fair comp_utils.
From trillium.fairness.examples.ticketlock Require Import ticketlock_model_lm client_model ticketlock_model fair_lock_lm lm_restr client_trace_termination. 

(* client_model_fair_term *)

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

  Let cmft_instance :=
        @client_model_fair_term _ _ _ _ tl_gs_size _ _ TlLM2_LGF
          _ TlLM2_LF
          TlLM2_nexts _ _ _ Tl_FL_LM
          _ _ PKE. 


  Theorem client_terminates
    (extr : heap_lang_extrace)
    (Hvex : extrace_valid extr)
    (Hexfirst : (trfirst extr).1 = [client #()]):
    (∀ tid, fair_ex tid extr) -> terminating_trace extr.
  Proof.
    set (Σ := gFunctors.app (heapΣ (@LM_EM_HL _ _ client_model LF')) clientPreΣ).
    assert (heapGpreS Σ (@LM_EM_HL _ _ client_model LF')) as HPreG.
    { apply _. }
    set (st0 := (δ_lib0, 3): fmstate client_model_impl).
    assert (initial_ls_LSI st0 0 (LM := client_model)) as LSI0.
    { subst st0. red. red.
      intros gi [ρ MAP]. simpl in MAP.
      by rewrite δ_lib0_map in MAP. }
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



