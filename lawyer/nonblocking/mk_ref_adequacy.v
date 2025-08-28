From lawyer.nonblocking Require Import mk_ref wfree_adequacy wfree_traces.

Theorem mk_ref_is_wait_free: wait_free mk_ref (fun _ => True).
Proof using.
  pose proof (wfree_is_wait_free _ mk_ref_WF_spec).
  simpl in H. apply H. 
Qed.

(* Print Assumptions mk_ref_is_wait_free.  *)
