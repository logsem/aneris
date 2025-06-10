From iris.proofmode Require Import tactics coq_tactics.
From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre ectx_lifting.
From fairness Require Import locales_helpers utils. 
From heap_lang Require Export heap_lang_defs tactics notation sswp_logic locales_helpers_hl.
From lawyer Require Import program_logic.
From iris.base_logic.lib Require Import invariants.


Section Tests.
  Context `{EM: ExecutionModel heap_lang M}. 
  Context `{hGS: @heapGS Σ _ EM}.

  Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).

  Lemma MU_inv_alloc E τ P Q ι:
    MU E τ (Q ∗ P) -∗ MU E τ (Q ∗ inv ι P).
  Proof using.
    iIntros "MU".
    rewrite /MU /MU_impl. iIntros (??) "TI".
    iMod ("MU" with "TI") as (??) "(TI & Q & P)". 
    iMod (inv_alloc with "[P]") as "INV".
    { iNext. iApply "P". }
    iModIntro. do 2 iExists _. iFrame "#∗".
  Qed.

End Tests.  
    
    
