From iris.proofmode Require Import proofmode coq_tactics tactics.
From heap_lang Require Import lang.
From lawyer Require Import program_logic.
From lawyer.nonblocking Require Import pwp.


Ltac solve_vcs := 
  match goal with
    |- vals_compare_safe ?x ?y => red; set_solver
  end. 

Ltac pwp_pure_step :=
    try (iEval (rewrite /pwp));
    try (iApply trillium.program_logic.weakestpre.wp_value; []);
    try (wp_bind (Rec _ _ _)%E || wp_bind (App _ _)%E);
    (iApply sswp_pwp; [done| ]; iApply sswp_pure_step; (try solve_vcs || done); [ ]; do 2 iModIntro; iEval (simpl) );
    try (iApply trillium.program_logic.weakestpre.wp_value; [] || iEval (rewrite /pwp)). 

Ltac pwp_pure_steps := repeat pwp_pure_step. 
