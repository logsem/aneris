From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel resources actual_resources heap_lang_defs em_lm em_lm_heap_lang lm_fair lm_fair_traces pmp_lifting trace_interp_corr.


Section ActualOwnershipInterface. 
  Context `{LM: LiveModel (locale heap_lang) M LSI_True}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.
  Context {LF: LMFairPre LM}. 
  Context`{invGS_gen HasNoLc Σ}.

  (* TODO: get rid of mim_* lemmas inside of actual_resources *)
  (* TODO: get rid of excessive shelved goals
     (could be solved by new implementation of LiveState) *)
  Lemma ActualOwnershipPartial:
    ⊢ PartialModelPredicates ∅ (EM := @LM_EM_HL _ _ _ LF) (iLM := LM) (eGS := fG).
    (* ⊢ LM_steps_gen ∅ τ g (EM := @LM_EM_HL _ _ _ LF) (iLM := LM) (eGS := fG) (relies_on := fun x y => ⌜ x = y ⌝).  *)
  Proof.
    iIntros. iApply (Build_PartialModelPredicates (EM := @LM_EM_HL _ _ _ LF)). 
    iModIntro. repeat iSplitL. 
    - iIntros (???????). iIntros "FUELS MSI". simpl in *.
      iDestruct "MSI" as "[LM_MSI %TR]".
      iDestruct (has_fuel_in with "FUELS LM_MSI") as %Hxdom; eauto.
      iMod (actual_update_no_step_enough_fuel with "FUELS LM_MSI") as (?) "(%STEPM & FUELS & LM_MSI' & %TMAP')".
      3: by apply empty_subseteq. 2: set_solver. 1: done.
      rewrite difference_empty_L. 
      iModIntro. do 2 iExists _. rewrite /em_lm_msi. iFrame.
      iPureIntro. split; try done. 
      2: { eapply (tids_dom_restrict_mapping _ _ _  _ _ STEP); eauto. }
      remember (trace_last auxtr) as δ1. 
      red. repeat split; eauto.
      * eexists. split; [apply STEPM| ]. done. 
      * eapply (tids_restrict_smaller' (LM := LM)).
        eapply (tids_dom_restrict_mapping _ _ _ _ _ STEP TR).
        eauto.
    - iIntros "* FUELS MSI". simpl in *.
      iDestruct "MSI" as "[LM_MSI %TR]".
      remember (trace_last auxtr) as δ1.
      pose proof (tids_restrict_smaller' _ _ TR) as SM.
      assert (Hnewζ: (locale_of tp1 efork) ∉ dom (ls_tmap δ1)).
      { subst δ1. rewrite LAST in SM. apply not_elem_of_dom. simpl in *.
        apply TR. 
        unfold tids_smaller in SM. 
        rewrite elem_of_list_fmap. intros ([??]&Hloc&Hin).
        symmetry in Hloc.
        rewrite -> prefixes_from_spec in Hin.
        destruct Hin as (?&t0&?&?).
        simplify_eq. list_simplifier.
        eapply locale_injective=>//.
        apply prefixes_from_spec.
        exists t0, []. split =>//. rewrite LAST in H1. by list_simplifier. }

      (* TODO: make it a lemma *)
      iAssert (⌜ (ls_tmap δ1 !! ζ = Some (dom fs)) ⌝)%I as %TMAPζ.
      { iDestruct "FUELS" as "[FRAG ?]".
        iDestruct "LM_MSI" as (?) "(?&AUTH&?&?)".
        simpl.
        iDestruct (frag_mapping_same with "AUTH FRAG") as "%MM".
        by rewrite dom_fmap_L in MM. }
      iDestruct (has_fuel_in with "FUELS LM_MSI") as %Hxdom; eauto.
      iMod (actual_update_fork_split with "FUELS LM_MSI") as (?) "(FUELS1 & FUELS2 & POST & LM_MSI' & %STEPM & %TMAP')"; eauto.
      do 2 iExists _. iFrame. iModIntro. iPureIntro.
      split.  
      + red. intros. eapply tids_dom_fork_step; eauto.
        * intros. apply TR. congruence.
        * inversion STEPM. destruct H1 as [? MM].
          eapply ls_mapping_tmap_corr in MM as (?&?&?).
          eapply elem_of_dom_2; eauto.
        * simpl.
          destruct POOL as (?&?&?).
          exists x, efork. done.
      + repeat split; eauto.
        { eexists; split; [apply STEPM| ]; done. }        
        eapply tids_smaller'_fork_step; [apply STEP| ..]. 
        * by rewrite -LAST.
        * eapply locale_trans_dom; eauto.
          eexists. split; [apply STEPM| ]. done. 
        * eauto. 
        * destruct POOL as (?&?&?).
          exists x, efork. done.
    - iIntros "* FUELS ST MSI FR". simpl in *.
      iDestruct "MSI" as "[LM_MSI %TR]".
      pose proof (tids_restrict_smaller' _ _ TR) as SM.
      iDestruct (model_agree' with "LM_MSI ST") as "%Heq".
      iDestruct (has_fuel_in with "FUELS LM_MSI") as %Hxdom; eauto.
      (* TODO: make it a lemma *)
      iAssert (⌜ fr1 ∩ dom (ls_fuel δ1) = ∅ ⌝)%I as %FR0.
      { iDestruct "LM_MSI" as (?) "(?&?&FR'&?&%)".
        iDestruct (free_roles_inclusion with "FR' FR") as "%".
        iPureIntro. set_solver. }
      iMod (actual_update_step_still_alive with "FUELS ST LM_MSI FR") as (?) "(%STEPM & FUELS & ST & LM_MSI & FR & %TMAP2)"; eauto. 
      iModIntro. do 2 iExists _. iFrame. iPureIntro. split.
      + repeat split; eauto.
        (* 2: by rewrite LAST2; eauto. *)
        { rewrite LAST2. eexists; split; [apply STEPM| ]. done. }  
        eapply tids_smaller'_model_step; eauto.
        eapply locale_trans_dom; eauto.
        eexists. split; [apply STEPM| ]. done. 
      + eapply tids_dom_restrict_mapping; eauto.
        Unshelve. all: eauto. 
  Qed.

End ActualOwnershipInterface.  
