From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import utils.
From lawyer.examples Require Import obls_tactics.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From lawyer.nonblocking.examples.queue Require Import simple_queue_utils simple_queue.
From lawyer.nonblocking.examples.queue.dequeuer Require Import dequeuer_lib.
From heap_lang Require Import heap_lang_defs lang notation.


Close Scope Z.


Definition read_head_dequeuer (sq: SimpleQueue): val := 
  λ: <>,
    let: "ch" := !#Head in
    let: "ct" := !#Tail in
    if: "ch" = "ct" then NONE
    else SOME (get_val "ch")
.


Section ReadHeadDequeuerLawyer.      

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.
  Context {QL: QueueG Σ}.
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}. 

  Context (d: Degree).
  Context (PE: val -> iProp Σ) {PERS_PE: forall v, Persistent (PE v)}.

  Let hGS: heap1GS Σ := iem_phys _ EM.
  Existing Instance hGS.
  Definition read_head_dequeuer_fuel := 100.

  Lemma read_head_dequeuer_spec (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ queue_inv PE ∗ dequeue_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d read_head_dequeuer_fuel }}}
       read_head_dequeuer q_sq #() @ CannotFork; NotStuck; τ; ⊤
    {{{ (v: val), RET v; th_phase_frag τ π q ∗ dequeue_token ∗ 
                         (⌜ v = NONEV ⌝ ∨ ∃ v', ⌜ v = SOMEV v' ⌝ ∗ PE v') }}}.
  Proof using PERS_PE.
    simpl. iIntros (Φ) "(#INV & TOK & PH & CPS) POST".
    rewrite /read_head_dequeuer.
    pure_steps.

    wp_bind (! _)%E.
    iMod (dequeuer_read_head_vs with "[$] [$]") as "(%h & %ph & %fl & HEAD & HEAD')". 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_load with "HEAD"). iIntros "!> HEAD".
    MU_by_burn_cp. iApply wp_value.
    iMod ("HEAD'" with "[$]") as "DR".
    iModIntro.

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (! _)%E.
    iMod (dequeuer_read_tail_vs with "[$] [$]") as "(%t & %br & %pt & TAIL & %ORDER & #HT & TAIL')". 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_load with "[$]"). iIntros "!> TAIL".
    MU_by_burn_cp. iApply wp_value.
    iMod ("TAIL'" with "[$]") as "DR".
    iModIntro. 
                        
    wp_bind (Rec _ _ _)%E. pure_steps.    

    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { set_solver. }
    MU_by_burn_cp. iApply wp_value.

    iDestruct "HT" as "[[%GE <-] | (%NEMPTY & %ndh & #HTH)]". 
    { assert (t = h) as ->.
      { red in ORDER. lia. }
      rewrite bool_decide_true; [| done].
      iMod (dequeuer_close with "[$] [$]") as "TOK".
      pure_steps. 
      iApply "POST". iFrame.
      by iLeft. }

    rewrite bool_decide_false; [| set_solver]. pure_steps.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].  
    iApply (get_head_val_spec with "[-POST CPS]").
    { done. }
    { iFrame "#∗". }
    iIntros "!> (PH & DR & PEh)".
    
    iMod (dequeuer_close with "[$] [$]") as "TOK".
    iApply sswp_MU_wp; [done| ]. 
    iApply sswp_pure_step; [done| ]. 
    MU_by_burn_cp. pure_steps.
    iApply "POST". iFrame.
    iRight. iExists _. iSplit; [done| ]. by iFrame. 
  Qed.

End ReadHeadDequeuerLawyer.


From lawyer.nonblocking Require Import pwp.
From lawyer.nonblocking.examples Require Import pwp_tactics. 

Section ReadHeadDequeuerPwp.
  Context {Σ} {hG: heap1GS Σ} {invG: invGS_gen HasNoLc Σ}. 
  
  Context {QL: QueueG Σ}.
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}.

  Context (PE: val -> iProp Σ) {PERS_PE: forall v, Persistent (PE v)}.

  Let iG := @irisG_looping _ HeapLangEM _ _ hG si_add_none.
  Existing Instance iG.

  Lemma read_head_dequeuer_pwp_spec (τ: locale heap_lang):
    {{{ queue_inv PE ∗ dequeue_token }}}
       read_head_dequeuer q_sq #() @ CannotFork; NotStuck; τ; ⊤
    {{{ (v: val), RET v; dequeue_token ∗ (⌜ v = NONEV ⌝ ∨ ∃ v', ⌜ v = SOMEV v' ⌝ ∗ PE v') }}}.
  Proof using PERS_PE.
    simpl. iIntros (Φ) "(#INV & TOK) POST".
    rewrite /read_head_dequeuer.
    pwp_pure_steps.

    wp_bind (! _)%E.
    iApply wp_atomic. 
    iMod (dequeuer_read_head_vs with "[$] [$]") as "(%h & %ph & %fl & HEAD & HEAD')".
    iModIntro. 
    iApply sswp_pwp; [done| ].
    iApply (wp_load with "HEAD"). iIntros "!> HEAD".
    iApply wp_value. iNext. 
    iMod ("HEAD'" with "[$]") as "DR".
    iModIntro.

    wp_bind (Rec _ _ _)%E. pwp_pure_steps.

    wp_bind (! _)%E.
    iApply wp_atomic. 
    iMod (dequeuer_read_tail_vs with "[$] [$]") as "(%t & %br & %pt & TAIL & %ORDER & #HT & TAIL')".
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
      iMod (dequeuer_close with "[$] [$]") as "TOK".
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
    iMod (dequeuer_close with "[$] [$]") as "TOK".
    iApply sswp_pwp; [done| ]. iModIntro.
    iApply sswp_pure_step; [done| ]. 
    do 2 iModIntro. iApply wp_value.
    iApply "POST". iFrame.
    iRight. iExists _. iSplit; [done| ]. by iFrame.     
  Qed.

End ReadHeadDequeuerPwp.
