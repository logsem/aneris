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
From lawyer.nonblocking.tokens Require Import om_wfree_inst_tokens. 

Close Scope Z.

Section QueueSpec.
  Context (SQ: SimpleQueue).
  Context (ph pfl: loc).

  Definition queue_ms: gmultiset val := {[+ enqueuer_thread SQ; dequeuer_thread SQ +]}.

  Definition queue_Σ: gFunctors := #[

  ].

  Program Definition SimpleQueue_WaitFreeToken: WaitFreeSpecToken queue_ms := {|
    wfst_is_init_st := is_init_queue_cfg SQ ph pfl #0;
    wfst_preG := QueuePreG;
    wfst_G := QueueG;
  |}.
