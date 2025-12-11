From heap_lang Require Import lang notation.
From lawyer.nonblocking Require Import counter list_map wfree_adequacy wfree_traces.


(* TODO: move *)
Lemma always_returns_impl m etr s1 s2
  (S12: stuckness_le s1 s2)
  :
  always_returns m s1 etr -> always_returns m s2 etr.
Proof using.
  rewrite /always_returns. simpl.
  intros AR [i tpc] **.
  ospecialize * (AR (trace_context.TraceCtx i tpc)); eauto.
  destruct AR as [| (->&?)]; [by left| ].
  destruct s2; try done. by right.
Qed.

(* TODO: move *)
Lemma wait_free_impl m C1 C2 s1 s2
  (C21: forall c, C2 c -> C1 c)
  (S12: stuckness_le s1 s2):
  wait_free m C1 s1 -> wait_free m C2 s2.
Proof using.
  From trillium.traces Require Import inftraces exec_traces. 
  rewrite /wait_free. simpl. intros WF ? INIT ??.
  eapply always_returns_impl; eauto.
Qed.
  

Theorem list_map_incr_is_wait_free
  (l0: loc := Loc 0)
  : wait_free (λ: "x", hl_list_map_cur (incr l0) "x")%V (counter_is_init_st l0) MaybeStuck.
Proof using.
  eapply wait_free_impl with (s1 := MaybeStuck).
  3: { apply wfree_is_wait_free. eauto. }
  2: done.
  Unshelve.
  2: { unshelve eapply hlm_WF_fix_spec_unsafe.
       { apply om_wfree_inst.WFS_weaken.
         apply counter_WF_spec. }
       2: { simpl. reflexivity. } }
  simpl. done.
Qed.

Print Assumptions list_map_incr_is_wait_free.
