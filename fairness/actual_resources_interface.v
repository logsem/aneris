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
    - iIntros. iApply (actual_update_no_step_enough_fuel with "[$] [$]"); eauto.
      all: set_solver. 
    - iIntros. iApply (actual_update_fork_split with "[$] [$]"); done.
    - iIntros. 
      iApply (actual_update_step_still_alive with "[$] [$] [$] [$]"); eauto.
    - iIntros. iApply (frag_free_roles_fuels_disj with "[$] [$] [$]").
  Defined.

End ActualOwnershipInterface.  
