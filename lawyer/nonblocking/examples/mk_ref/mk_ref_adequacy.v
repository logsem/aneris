From heap_lang Require Import lang.
From lawyer.nonblocking Require Import wfree_adequacy wfree_traces.
From lawyer.nonblocking.examples.mk_ref Require Import mk_ref.

Theorem mk_ref_is_wait_free: wait_free mk_ref (fun _ => True) NotStuck any_arg.
Proof using.
  eapply (wfree_is_wait_free _ _ mk_ref_WF_spec).
  eauto. 
Qed.

Print Assumptions mk_ref_is_wait_free.
