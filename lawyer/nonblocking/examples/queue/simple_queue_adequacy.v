From heap_lang Require Import lang notation.
From lawyer.nonblocking Require Import wfree_traces.
From lawyer.nonblocking.tokens Require Import wfree_adequacy_tokens.
From lawyer.nonblocking.examples.queue Require Import simple_queue_spec simple_queue init_queue.


Theorem simple_queue_is_restr_wait_free (sq: SimpleQueue) ph pfl: 
  wait_free_restr (queue_ms sq) (is_init_queue_cfg sq ph pfl #0) NotStuck any_arg. 
Proof using.
  eapply (wfree_token_is_wait_free_restr _ (SimpleQueue_WaitFreeToken sq ph pfl)).
  red. intros ? DOM%gmultiset_elem_of_dom.
  rewrite gmultiset_elem_of_disj_union !gmultiset_elem_of_singleton in DOM.
  destruct DOM as [-> | ->]; red; eauto.
Qed.

Print Assumptions simple_queue_is_restr_wait_free. 
