
From lawyer.nonblocking.examples.counter Require Import counter_adequacy.
From lawyer.nonblocking.examples.mk_ref Require Import mk_ref_adequacy.
From lawyer.nonblocking.examples.list_map Require Import list_map_adequacy.
From lawyer.nonblocking.examples.queue Require Import simple_queue_adequacy.


Definition wfree_results := (
  counter_is_wait_free,
  mk_ref_is_wait_free,
  list_map_incr_is_wait_free,
  simple_queue_is_restr_wait_free
). 

Goal True. 
  idtac "-------------------------------------------".
  idtac "The axioms used throughout the wait-freedom development:".
Abort. 


Print Assumptions wfree_results.
