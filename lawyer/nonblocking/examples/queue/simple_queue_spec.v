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
From lawyer.nonblocking.examples.queue Require Import simple_queue_utils simple_queue init_queue.
From lawyer.nonblocking.examples.queue.dequeuer Require Import dequeuer_thread. 
From lawyer.nonblocking.examples.queue.enqueuer Require Import enqueuer_thread. 
From heap_lang Require Import heap_lang_defs lang notation.
From lawyer.nonblocking.tokens Require Import om_wfree_inst_tokens tokens_ra. 

Close Scope Z.

Section QueueSpec.
  Context (SQ: SimpleQueue).
  Context (ph pfl: loc).

  Definition queue_ms: gmultiset val := {[+ enqueuer_thread SQ; dequeuer_thread SQ +]}.

  (* TODO: move all of this *)
  (**************************)
  Definition max_exact_Σ: gFunctors := #[ GFunctor (prodUR (excl_authUR nat) mono_natUR)].
  Global Instance max_exact_sub: forall Σ, subG max_exact_Σ Σ -> MaxExactPreG Σ.
  Proof using. solve_inG. Qed. 
  
  Definition hist_queue_Σ: gFunctors := #[ GFunctor (authUR (gmapUR nat (agreeR HistNode)))].
  Global Instance hist_queue_sub: forall Σ, subG hist_queue_Σ Σ -> HistQueuePreG Σ.
  Proof using. solve_inG. Qed. 


  Definition read_hist_Σ: gFunctors := #[ GFunctor (authUR (gmapUR nat (prodR
                                    (optionR $ prodR (agreeR nat) max_natUR)
                                    (optionR read_state_cmra)
                                    )))].
  Global Instance read_hist_sub: forall Σ, subG read_hist_Σ Σ -> ReadHistPreG Σ.
  Proof using. solve_inG. Qed. 

  (* q_pre_dangle_rop ::  inG Σ (excl_authUR (option nat)); *)
  (* q_pre_tok :: inG Σ (exclR unitO); *)

  (* Instance queue_tokens_pre: SimpleQueueTokensPre mt_Σ. *)
  Instance queue_tokens_pre: forall Σ, subG mt_Σ Σ -> SimpleQueueTokensPre Σ.
  Proof using SQ.
    constructor.
    iMod (mt_init queue_ms) as "(%MT & TOKS)". iModIntro.
    iExists (SQT _ _ _ _ _ _ _).
    rewrite /queue_ms. rewrite methods_toks_split.
    rewrite bi.sep_comm. iApply "TOKS".
    Unshelve.
    3, 4: by apply _.
    1, 2: rewrite bi.wand_curry; rewrite -methods_toks_split;
      iIntros "X"; iDestruct (methods_toks_sub with "X") as %V;
      multiset_solver.
  Qed. 

  Definition queue_Σ: gFunctors := #[
    max_exact_Σ;
    GFunctor (exclR unitO);
    hist_queue_Σ;
    read_hist_Σ; 
    GFunctor (excl_authUR (option nat));
    mt_Σ
  ].

  Global Instance queue_sub: forall Σ, subG queue_Σ Σ -> QueuePreG Σ.
  Proof using SQ. solve_inG. Qed. 

  (**************************)

  Program Definition SimpleQueue_WaitFreeToken: WaitFreeSpecToken queue_ms := {|
    wfst_is_init_st := is_init_queue_cfg SQ ph pfl #0;
    wfst_preG := QueuePreG;
    wfst_G := QueueG;
    wfst_Σ := queue_Σ;
    wfst_mod_inv := 
  |}.
