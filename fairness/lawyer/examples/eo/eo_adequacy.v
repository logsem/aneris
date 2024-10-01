From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import locales_helpers comp_utils trace_lookup fairness.
From trillium.fairness.heap_lang Require Import simulation_adequacy notation.
From trillium.fairness.lawyer Require Import counter_model sub_action_em.


Definition eo_prog: val.
Admitted. 

Definition eo_ex_progress (l: loc) (extr : heap_lang_extrace) :=
  ∀ (i: nat), ∃ n c, extr S!! n = Some c /\ heap (c.2) !! l = Some #i. 

Definition eo_ex_mono (l: loc) (extr : heap_lang_extrace) :=
  ∀ n, ∃ c c' oτ (i j: nat),
    extr !! n = Some (c, Some (oτ, c')) /\
    heap c.2 !! l = Some #i /\
    heap c'.2 !! l = Some #j /\
    i <= j
.

Section EOAdequacy.

  Definition eoΣ: gFunctors.
  Admitted. 

  Theorem eo_progress
    (l: loc)
    (extr : heap_lang_extrace)
    (Hexfirst : trfirst extr = ([eo_prog #0], {| heap := {[l:=#0]}; used_proph_id := ∅ |})):
    (* (∀ tid, fair_ex tid extr) -> terminating_trace extr. *)
    extrace_fairly_terminating extr. 
  Proof using.
    assert (heapGpreS eoΣ EM) as HPreG.
    { apply _. }

    destruct (trfirst extr) as [tp_ σ1] eqn:EX0. simpl in *. subst tp_.                
    
    set (s1 := init_om_state (EO_OP LIM) (trfirst extr)). 
    
    unshelve epose proof (simple_om_simulation_adequacy_terminate (EO_OP LIM) eofinΣ NotStuck
                  _ _ _ _
                  _ _ EX0) as FAIR_TERM; eauto.
    { exact tt. }
    { simpl. subst s1. rewrite EX0. apply init_om_state_init. }
    
    apply FAIR_TERM.
    red. intros ?. iStartProof. iIntros "[HEAP INIT] !>".
    iSplitL.
    - admit.
    - subst s1. rewrite EX0. iApply om_sim_RAH. 
  Admitted. 

End EOAdequacy.
