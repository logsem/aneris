From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import utils.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From lawyer Require Import program_logic.
From lawyer.nonblocking Require Import pwp.
From lawyer.nonblocking.examples Require Import pwp_tactics. 
From lawyer.nonblocking.examples.queue Require Import simple_queue_utils simple_queue.
From lawyer.nonblocking.examples.queue.dequeuer Require Import dequeuer_lib read_head_dequeuer.
From heap_lang Require Import heap_lang_defs lang notation.


Close Scope Z.


Section ReadHeadDequeuer.      
  Context {Σ} {hG: heap1GS Σ} {invG: invGS_gen HasNoLc Σ}. 
  
  Context {QL: QueueG Σ}.
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}.

  Context (PE: val -> iProp Σ) {PERS_PE: forall v, Persistent (PE v)}.

  Let iG := @irisG_looping _ HeapLangEM _ _ hG si_add_none.
  Existing Instance iG.

  Lemma read_head_dequeuer_spec (τ: locale heap_lang):
    {{{ queue_inv PE ∗ dequeue_token }}}
       read_head_dequeuer q_sq #() @ CannotFork; NotStuck; τ; ⊤
    {{{ (v: val), RET v; (⌜ v = NONEV ⌝ ∨ ∃ v', ⌜ v = SOMEV v' ⌝ ∗ PE v') }}}.
  Proof using PERS_PE.
    simpl. iIntros (Φ) "(#INV & TOK) POST".
    rewrite /read_head_dequeuer.
    pwp_pure_steps.

    wp_bind (! _)%E.
    iApply wp_atomic. 
    iMod (read_head_dequeuer_read_head_vs with "[$] [$]") as "(%h & %ph & %fl & HEAD & HEAD')".
    iModIntro. 
    iApply sswp_pwp; [done| ].
    iApply (wp_load with "HEAD"). iIntros "!> HEAD".
    iApply wp_value. iNext. 
    iMod ("HEAD'" with "[$]") as "DR".
    iModIntro.

    wp_bind (Rec _ _ _)%E. pwp_pure_steps.

    wp_bind (! _)%E.
    iApply wp_atomic. 
    iMod (read_head_dequeuer_read_tail_vs with "[$] [$]") as "(%t & %br & %pt & TAIL & %ORDER & #HT & TAIL')".
    iModIntro.
    iApply sswp_pwp; [done| ].
    iApply (wp_load with "[$]"). iIntros "!> TAIL".
    iApply wp_value. iModIntro. 
    iMod ("TAIL'" with "[$]") as "DR".
    iModIntro. 
                        
    wp_bind (Rec _ _ _)%E. pwp_pure_steps.

    wp_bind (_ = _)%E.
    iApply sswp_pwp; [done| ].
    iApply sswp_pure_step.
    { set_solver. }
    do 2 iModIntro. iApply wp_value.

    iDestruct "HT" as "[[%GE <-] | (%NEMPTY & %ndh & #HTH)]". 
    { assert (t = h) as ->.
      { red in ORDER. lia. }
      rewrite bool_decide_true; [| done].
      iApply fupd_wp.
      iMod (read_head_dequeuer_close with "[$] [$]") as "TOK".
      iModIntro.
      pwp_pure_steps. 
      iApply "POST". iFrame.
      by iLeft. }

    rewrite bool_decide_false; [| set_solver]. pwp_pure_steps.
    wp_bind (get_val _)%E.
    iApply (get_head_val_pwp_spec with "[-POST]").
    { done. }
    { iFrame "#∗". }
    iIntros "!> (DR & PEh)".

    iApply fupd_wp.
    iMod (read_head_dequeuer_close with "[$] [$]") as "TOK".
    iApply sswp_pwp; [done| ]. iModIntro.
    iApply sswp_pure_step; [done| ]. 
    do 2 iModIntro. iApply wp_value.
    iApply "POST". iFrame.
    iRight. iExists _. iSplit; [done| ]. by iFrame.     
  Qed.

End ReadHeadDequeuer.
