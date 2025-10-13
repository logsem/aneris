From heap_lang Require Import lang.
From lawyer.nonblocking Require Import counter wfree_adequacy wfree_traces.

Theorem counter_is_wait_free
  (l0: loc := Loc 0)
  : wait_free (incr l0) (counter_is_init_st l0).
Proof using.
  pose proof (wfree_is_wait_free _ (counter_WF_spec l0)).
  done.
Qed.

(* Print Assumptions counter_is_wait_free.  *)
