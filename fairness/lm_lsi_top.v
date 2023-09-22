From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness resources heap_lang_defs em_lm em_lm_heap_lang lm_steps_gen.
From trillium.fairness.lm_rules Require Import fuel_step.

Section LMLSITopLevel. 
  Context `{LM: LiveModel (locale heap_lang) M LSI}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.
  Context`{invGS_gen HasNoLc Σ}. 

  Lemma lm_lsi_toplevel:
    ⊢ LM_steps_gen ∅ (EM := @LM_EM_HL _ _ LM) (iLM := LM) (PMPP := ActualOwnershipPartialPre) (eGS := fG). 
  Proof.
    iIntros. iApply (Build_LM_steps_gen (EM := @LM_EM_HL _ _ LM)). 
    iModIntro. repeat iSplitL.
    - iIntros "* FUELS ST MSI". simpl in *.
      iDestruct "MSI" as "[LM_MSI %TR]".
      iDestruct (has_fuel_in with "FUELS LM_MSI") as %Hxdom; eauto.
      iPoseProof (model_agree' with "LM_MSI ST") as "%ST_EQ". 
      iMod (actual_update_no_step_enough_fuel_drop with "FUELS ST LM_MSI") as (?) "(%STEPM & FUELS & ST & LM_MSI' & %TMAP')"; eauto. 
      { by rewrite ST_EQ. } 
      iModIntro. do 2 iExists _. rewrite /em_lm_msi. iFrame.
      iPureIntro. split.
      + remember (trace_last auxtr) as δ1. 
        pose proof (tids_restrict_smaller _ _ TR) as SM.
        repeat split; eauto.
        * done.
        * eapply tids_smaller_restrict_mapping; eauto.
          simpl. erewrite (maps_inverse_match_uniq1 (ls_mapping δ2)).
          3: { eapply (mim_fuel_helper _ rem); eauto.
               eapply ls_mapping_tmap_corr. }
          { apply map_filter_subseteq. }
          erewrite <- TMAP'. apply ls_mapping_tmap_corr.
      + eapply tids_dom_restrict_mapping; eauto.
    - admit. 
    - admit. 
    - admit. 
  Admitted. 

End LMLSITopLevel.
