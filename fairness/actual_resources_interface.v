From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel resources actual_resources heap_lang_defs em_lm pmp_lifting.

Section ActualOwnershipInterface. 
  Context `{LM: LiveModel heap_lang M}.
  (* Context `{Countable (locale Λ)}. *)
  (* Context `{EqDecision (expr Λ)}. *)
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.
  Context`{invGS_gen HasNoLc Σ}. 

  Lemma ActualOwnershipPartial:
    ⊢ PartialModelPredicates ∅ (EM := @LM_EM _ LM) (iLM := LM) (PMPP := ActualOwnershipPartialPre) (eGS := fG). 
  Proof.
    iIntros. iApply Build_PartialModelPredicates. iModIntro. repeat iSplitL.
    - iIntros. iApply (actual_update_no_step_enough_fuel with "[$]"); set_solver.
    - iIntros. iMod (actual_update_fork_split with "[$] [$]") as (?) "?"; eauto.
    - iIntros "*". iIntros.
      iApply (actual_update_step_still_alive with "[$] [$] [$] [$]"); eauto.
    - iIntros. iApply (frag_free_roles_fuels_disj with "[$] [$] [$]").
    - iIntros. iExists _. iFrame.
      iIntros. do 2 iExists _. by iFrame.
  Defined.

End ActualOwnershipInterface.  
