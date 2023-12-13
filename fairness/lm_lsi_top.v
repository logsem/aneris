From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness resources heap_lang_defs em_lm em_lm_heap_lang lm_steps_gen lm_fair lm_fair_traces.
From trillium.fairness.lm_rules Require Import fuel_step fork_step model_step.

Section LMLSITopLevel. 
  Context `{LM: LiveModel (locale heap_lang) M LSI}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.
  Context {LF': LMFairPre' LM}. 
  Context`{invGS_gen HasNoLc Σ}. 

  Local Instance LF: LMFairPre LM.
  esplit; apply _.
  Defined. 

  (* TODO: move *)
  Lemma mim_lookup_helper `{Countable K, Countable V, EqDecision K}
    (tm: gmap V (gset K)) (m: gmap K V)
    R ζ
    (MIM: maps_inverse_match m tm)
    (NE: R ≠ ∅)
    (DOM: ∀ ρ, m !! ρ = Some ζ ↔ ρ ∈ R):
    tm !! ζ = Some R.
  Proof. 
    apply finitary.set_choose_L' in NE as [k INR].
    pose proof (proj2 (DOM k) INR) as MAP.
    red in MIM. specialize MIM with (v := ζ). 
    pose proof (proj1 (MIM _ ) MAP) as (R' & TM' & IN').
    rewrite TM'. f_equal.
    apply set_eq. clear dependent k. intros k.
    rewrite <- DOM. rewrite TM' in MIM. split.
    - intros IN'. apply MIM. eauto.
    - intros ?%MIM. set_solver.
  Qed. 

  Lemma lm_lsi_toplevel:
    ⊢ LM_steps_gen ∅ (EM := @LM_EM_HL _ _ _ LF') (iLM := LM) (PMPP := ActualOwnershipPartialPre) (eGS := fG). 
  Proof.
    iIntros. iApply (Build_LM_steps_gen (EM := @LM_EM_HL _ _ _ LF')). 
    iModIntro. repeat iSplitL.
    - iModIntro. iIntros "* FUELS ST MSI". simpl in *.
      iDestruct "MSI" as "[LM_MSI %TR]".
      iDestruct (has_fuel_in with "FUELS LM_MSI") as %Hxdom; eauto.
      iPoseProof (model_agree' with "LM_MSI ST") as "%ST_EQ". 
      iMod (actual_update_no_step_enough_fuel_drop with "FUELS ST LM_MSI") as (?) "(%STEPM & FUELS & ST & LM_MSI' & %TMAP')"; eauto. 
      { by rewrite ST_EQ. } 
      iModIntro. do 2 iExists _. rewrite /em_lm_msi. iFrame.
      iPureIntro. split.
      + remember (trace_last auxtr) as δ1. 
        pose proof (tids_restrict_smaller' _ _ TR) as SM.
        repeat split; eauto.
        * eexists. split; [apply STEPM| ]; done. 
        * eapply tids_smaller'_restrict_mapping; eauto.
          rewrite TMAP'.
          rewrite dom_insert. rewrite subseteq_union_1; [done| ].
          apply singleton_subseteq_l.
          eapply locale_trans_dom; eauto.
          eexists. split; eauto.
          { apply STEPM. }
          done. 
      + eapply tids_dom_restrict_mapping; eauto.
    - iModIntro. iIntros "* FUELS MSI". simpl in *.
      iDestruct "MSI" as "[LM_MSI %TR]".
      iDestruct (has_fuel_in with "FUELS LM_MSI") as %Hxdom; eauto.
      (* iPoseProof (model_agree' with "LM_MSI ST") as "%ST_EQ".  *)
      iMod (actual_update_no_step_enough_fuel_keep with "FUELS LM_MSI") as (?) "(%STEPM & FUELS & LM_MSI' & %TMAP')"; eauto.
      rewrite gmap_filter_dom_id. 
      iModIntro. do 2 iExists _. rewrite /em_lm_msi. iFrame.
      iPureIntro. split.
      + remember (trace_last auxtr) as δ1. 
        pose proof (tids_restrict_smaller' _ _ TR) as SM.
        repeat split; eauto.
        * eexists. split; [apply STEPM| ]; done. 
        * eapply tids_smaller'_restrict_mapping; eauto.
          by rewrite TMAP'.
      + eapply tids_dom_restrict_mapping; eauto.
        rewrite TMAP'.
        rewrite dom_fmap_L in Hxdom.
        exists (dom fs).
        symmetry. apply insert_id.
        eapply mim_lookup_helper; eauto. 
        apply ls_mapping_tmap_corr.         
    - iModIntro. iIntros "* FUELS ST MSI FR". simpl in *.
      iDestruct "MSI" as "[LM_MSI %TR]".
      pose proof (tids_restrict_smaller' _ _ TR) as SM.
      iDestruct (model_agree' with "LM_MSI ST") as "%Heq".
      iDestruct (has_fuel_in with "FUELS LM_MSI") as %Hxdom; eauto.
      (* TODO: make it a lemma *)
      iAssert (⌜ fr1 ∩ dom (ls_fuel δ1) = ∅ ⌝)%I as %FR0.
      { iDestruct "LM_MSI" as (?) "(?&?&FR'&?&%)".
        iDestruct (free_roles_inclusion with "FR' FR") as "%".
        iPureIntro. set_solver. }
      iMod (actual_update_step_still_alive_gen with "FUELS ST LM_MSI FR") as (?) "(%STEPM & FUELS & ST & LM_MSI & FR & %TMAP2)"; eauto. 
      iModIntro. do 2 iExists _. iFrame. iPureIntro. split.
      + repeat split; eauto.
        (* 2: by rewrite LAST2; eauto. *)
        { rewrite LAST2. eexists; split; [apply STEPM| ]. done. }  
        eapply tids_smaller'_model_step; eauto.
        eapply locale_trans_dom; eauto.
        eexists. split; [apply STEPM| ]. done. 
      + eapply tids_dom_restrict_mapping; eauto.
        Unshelve. all: eauto. 
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
      iMod (actual_update_fork_split_gen with "FUELS LM_MSI") as (?) "(FUELS1 & FUELS2 & POST & LM_MSI' & %STEPM & %TMAP')"; eauto.
      do 2 iExists _. iFrame. iModIntro. iPureIntro. split.
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
        eapply tids_smaller'_fork_step; eauto.
        * by rewrite -LAST.
        * eapply locale_trans_dom; eauto.
          eexists. split; [apply STEPM| ]. done.  
        * destruct POOL as (?&?&?).
          exists x, efork. done.
          Unshelve.
          2: exact LM. 
  Qed. 

End LMLSITopLevel.
