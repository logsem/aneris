From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel resources actual_resources. 

Section ActualOwnershipInterface. 
  Context `{LM: LiveModel Λ M}.
  Context `{Countable (locale Λ)}.
  Context `{EqDecision (expr Λ)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.
  Context`{invGS_gen HasNoLc Σ}. 

  Lemma ActualOwnershipPartial:
    ⊢ PartialModelPredicates ∅ (LM := LM) (iLM := LM) (PMPP := ActualOwnershipPartialPre). 
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
