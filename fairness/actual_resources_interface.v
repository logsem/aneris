From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel resources actual_resources heap_lang_defs em_lm pmp_lifting.


(* TODO: move *)
Section Utils.
  Context `{Countable K, Countable V, EqDecision K}.
  
  Lemma maps_inverse_match_subseteq (m1 m2: gmap K V) (m1' m2': gmap V (gset K))
    (M1: maps_inverse_match m1 m1') (M2: maps_inverse_match m2 m2')
    (SUB: dom m1' ⊆ dom m2')
    (INCL: forall v S1 S2, m1' !! v = Some S1 -> m2' !! v = Some S2 -> S1 ⊆ S2):
    m1 ⊆ m2.
  Proof.
    red in M1, M2. apply map_subseteq_spec. intros.
    specialize (proj1 (M1 _ _) H1) as [? [L1 ?]]. 
    apply M2.
    specialize (SUB x (elem_of_dom_2 _ _ _ L1)).
    apply elem_of_dom in SUB as [? ?].
    eexists. split; eauto. set_solver.
  Qed. 

End Utils.

Section ActualOwnershipInterface. 
  Context `{LM: LiveModel heap_lang M}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.
  Context`{invGS_gen HasNoLc Σ}. 

  (* TODO: replace Definitions with Lets in pmp_lifting.v *)
  Lemma ActualOwnershipPartial:
    ⊢ PartialModelPredicates ∅ (EM := @LM_EM _ LM) (iLM := LM) (PMPP := ActualOwnershipPartialPre) (eGS := fG). 
  Proof.
    iIntros. iApply Build_PartialModelPredicates. iModIntro. repeat iSplitL.
    - iIntros. rewrite /update_no_step_enough_fuel_def. 
      iIntros "FUELS MSI". simpl in *.
      iDestruct "MSI" as "[LM_MSI %TR]".
      iDestruct (has_fuel_in with "FUELS LM_MSI") as %Hxdom; eauto.
      iMod (actual_update_no_step_enough_fuel with "FUELS LM_MSI") as (?) "(%STEPM & FUELS & LM_MSI' & %TMAP')".
      3: by apply empty_subseteq. 2: set_solver. 1: done. 
      iModIntro. do 2 iExists _. rewrite /em_lm_msi. iFrame.
      iPureIntro. split.
      + remember (trace_last auxtr) as δ1. 
        pose proof (tids_restrict_smaller _ _ TR) as SM.
        repeat split; eauto.
        * done.
        * eapply tids_smaller_restrict_mapping; eauto.
          erewrite (maps_inverse_match_uniq1 (ls_mapping δ2)).
          3: { eapply (mim_fuel_helper _ ∅); eauto.
               { set_solver. }
               eapply ls_mapping_tmap_corr. }
          { apply map_filter_subseteq. }
          erewrite <- TMAP'. apply ls_mapping_tmap_corr.
      + eapply tids_dom_restrict_mapping; eauto.        
    - iIntros. rewrite /update_fork_split_def. 
      iIntros "FUELS MSI". simpl in *.
      iDestruct "MSI" as "[LM_MSI %TR]".
      remember (trace_last auxtr) as δ1.
      pose proof (tids_restrict_smaller _ _ TR) as SM.
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
        * done.
        * eapply tids_smaller_fork_step; eauto.
          ** by rewrite -LAST.
          ** erewrite (maps_inverse_match_uniq1 (ls_mapping δ2)).
             3: { eapply mim_helper_fork_step.
                  6: eapply (ls_mapping_tmap_corr δ1).
                  all: eauto.
                  rewrite dom_fmap_L in Hxdom.
                  apply elem_of_subseteq. intros.
                  apply Hxdom in H0.
                  apply elem_of_dom. eauto. }
             { eauto. }
             rewrite -TMAP'. apply ls_mapping_tmap_corr.
          ** destruct POOL as (?&?&?).
             exists x, efork. done.
    - 
                  


    (* - iIntros "*". iIntros. *)
    (*   iApply (actual_update_step_still_alive with "[$] [$] [$] [$]"); eauto. *)
    (* - iIntros. iApply (frag_free_roles_fuels_disj with "[$] [$] [$]"). *)
    (* - iIntros. iExists _. iFrame. *)
    (*   iIntros. do 2 iExists _. by iFrame. *)
  Defined.


End ActualOwnershipInterface.  



        (* iPureIntro. split. *)
        (* { intros. eapply tids_dom_fork_step; eauto. *)
        (*   2: admit. *)
        (*   congruence. } *)

    (* { iPureIntro. *)
    (*   eapply tids_smaller_fork_step; eauto. *)
    (*   2: admit. *)
    (*   erewrite build_LS_ext_spec_mapping; eauto. } *)
