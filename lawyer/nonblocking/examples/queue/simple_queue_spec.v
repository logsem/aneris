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
From lawyer.nonblocking.examples.queue Require Import simple_queue_utils simple_queue init_queue wrappers_lib.
From lawyer.nonblocking.tokens Require Import om_wfree_inst_tokens tokens_ra.
From lawyer.nonblocking.examples.queue.dequeuer Require Import dequeuer_thread. 
From lawyer.nonblocking.examples.queue.enqueuer Require Import enqueuer_thread. 
From heap_lang Require Import heap_lang_defs lang notation.

Close Scope Z.

Section QueueSpec.
  Context (SQ: SimpleQueue).
  Context (ph pfl: loc).

  Definition queue_ms: gmultiset val := {[+ enqueuer_thread SQ; dequeuer_thread SQ +]}.

  (* Instance queue_tokens_pre: SimpleQueueTokensPre mt_Σ. *)
  Program Instance mt_sqt Σ (MT: MethodToken queue_ms Σ): SimpleQueueTokens Σ := 
    {| dequeue_token := method_tok (dequeuer_thread SQ);
       read_head_token := method_tok (enqueuer_thread SQ); |}.
  Solve Obligations with 
    intros; rewrite bi.wand_curry; rewrite -methods_toks_split;
    iIntros "X"; iDestruct (methods_toks_sub with "X") as %V;
    multiset_solver.
  Fail Next Obligation. 

  Existing Instance mt_sqt. 

  Lemma init_queue_inv {Σ} {hGS: heap1GS Σ} {iGS: invGS_gen HasNoLc Σ}
    {MTPre: MethodTokenPre Σ} {QPre: QueuePreG Σ}:
      ∀ c, is_init_queue_cfg SQ ph pfl #0 c → 
            hl_phys_init_resource c ={⊤}=∗ 
            ∃ (MT: MethodToken queue_ms Σ) (_: QueueG Σ),
              queue_inv val_is_int ∗ methods_toks queue_ms (H := MT).
  Proof using.
    iIntros (c INIT) "HEAP".
    iMod (mt_init queue_ms) as "(%MT & TOKS)". 
    iDestruct (obtain_queue_init_resource with "[$]") as "QI"; eauto.
    iMod (queue_init val_is_int with "QI []") as "(%QQ & QI)".
    { set_solver. }
    by iFrame.
  Qed.
 
  Program Definition SimpleQueue_WaitFreeToken: WaitFreeSpecToken queue_ms := {|
    wfst_is_init_st := is_init_queue_cfg SQ ph pfl #0;
    wfst_preG := QueuePreG;
    wfst_G := QueueG;
    wfst_Σ := queue_Σ;
    wfst_subG := queue_sub;
    wfst_mod_inv _ _ _ _ _ := queue_inv val_is_int;
    wfst_init_mod _ _ _ _ _ := init_queue_inv;
    wfst_F := max et_fuel dt_fuel;
  |}.
  Next Obligation.
    iIntros "* #INV".
    iApply big_sepS_forall. iIntros (m DOM).
    rewrite /method_spec_token. iIntros (???? Φ) "!> (CPS & PH & TOK) POST".
    apply gmultiset_elem_of_dom in DOM. rewrite /queue_ms in DOM.
    rewrite gmultiset_elem_of_disj_union !gmultiset_elem_of_singleton in DOM.
    destruct DOM as [-> | ->].
    - split_cps "CPS" et_fuel.
      replace CannotFork with CanFork by admit.
      iApply (enqueuer_thread_spec with "[-POST]").
      { iFrame "#∗". }
      iIntros "!> %v (PH & RH & %GV)".
      iApply "POST". iFrame.
    - split_cps "CPS" et_fuel.
      replace CannotFork with CanFork by admit.
      iApply (dequeuer_thread_spec with "[-POST]").
      { iFrame "#∗". }
      iIntros "!> %v (PH & RH & %GV)".
      iApply "POST". iFrame.
  Admitted.
  Final Obligation. 
  Admitted. 

End QueueSpec. 
