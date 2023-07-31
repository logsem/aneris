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
    (* - iIntros. iMod (actual_update_fork_split with "[$] [$]") as (?) "?"; eauto. *)
    (* - iIntros "*". iIntros. *)
    (*   iApply (actual_update_step_still_alive with "[$] [$] [$] [$]"); eauto. *)
    (* - iIntros. iApply (frag_free_roles_fuels_disj with "[$] [$] [$]"). *)
    (* - iIntros. iExists _. iFrame. *)
    (*   iIntros. do 2 iExists _. by iFrame. *)
  Defined.


End ActualOwnershipInterface.  
