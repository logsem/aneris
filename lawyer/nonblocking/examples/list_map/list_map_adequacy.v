From heap_lang Require Import lang notation.
From lawyer.nonblocking Require Import wfree_adequacy wfree_traces.
From lawyer.nonblocking.examples.list_map Require Import list_map.
From lawyer.nonblocking.examples.counter Require Import counter.

  

Theorem list_map_incr_is_wait_free
  (l0: loc := Loc 0) :
  wait_free (λ: "x", hl_list_map_cur (incr l0) "x")%V
    (counter_is_init_st l0) MaybeStuck any_arg.
Proof using.
  eapply wait_free_impl with (s1 := MaybeStuck).
  3: done. 
  3: { apply wfree_is_wait_free. eauto. }
  2: done.
  Unshelve.
  2: { unshelve eapply hlm_WF_fix_spec_unsafe.
       { apply om_wfree_inst.WFS_weaken.
         apply counter_WF_spec. }
       2: { simpl. reflexivity. } }
  simpl. done.
Qed.

(* Print Assumptions list_map_incr_is_wait_free. *)
