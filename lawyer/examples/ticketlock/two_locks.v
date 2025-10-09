From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import utils.
From lawyer.examples Require Import obls_tactics.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From lawyer Require Import sub_action_em program_logic.
From lawyer.examples.ticketlock Require Import obls_atomic releasing_lock.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


(** With the current proof, we don't require anything from Σ before OM is instantiated.
    However, we keep this preG/G pattern for uniformness. *)
Class ClientPreG (Σ: gFunctors) := { }.

Class ClientG Σ := {
    cl_PreG :: ClientPreG Σ;
}.

Section MotivatingClient.
  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}. 

  Context (RFL1 RFL2: ReleasingFairLock).

  (** Lock 1 is acquired first. 
      The obligation to release it will be held while the second lock is acquired and released.
      Therefore, the levels of the first lock are bigger. *)
  Context (LOCKS_ORDER: forall l1 l2, l1 ∈ rfl_lvls RFL1 -> l2 ∈ rfl_lvls RFL2 -> lvl_lt l2 l1).

  Context (d__cl: Degree).
  Let d1 := (rfl_d RFL1). 
  Let d2 := (rfl_d RFL2). 
  Context (DEG1: deg_lt d1 d__cl) (DEG2: deg_lt d2 d__cl). 

  Definition acquire_two: val :=
    λ: "lk1" "lk2",
      (rfl_acquire RFL1) "lk1" ;;
      (rfl_acquire RFL2) "lk2"
    .

  Definition release_two: val :=
    λ: "lk1" "lk2",
      (rfl_release RFL2) "lk2" ;;
      (rfl_release RFL1) "lk1"
    .

  Definition thread: val :=
    λ: "lk1" "lk2",
      acquire_two "lk1" "lk2" ;;
      release_two "lk1" "lk2"
  .

  Definition client_two: val := 
    λ: <>,
      let: "lk1" := rfl_newlock RFL1 #() in
      let: "lk2" := rfl_newlock RFL2 #() in
      (Fork (thread "lk1" "lk2") ;;
       Fork (thread "lk1" "lk2"))
  .      

  Section AfterInit.
    Context {CL: ClientG Σ}.
    Context {RFLG1: rfl_G RFL1 Σ} {RFLG2: rfl_G RFL2 Σ}.

    Definition two_locks lk1 lk2: iProp Σ :=
      rfl_is_lock RFL1 lk1 0 emp (rfl_G0 := RFLG1) ∗ rfl_is_lock RFL2 lk2 0 emp (rfl_G0 := RFLG2).

    Instance two_locks_pers lk1 lk2: Persistent (two_locks lk1 lk2).
    Proof using.
      apply bi.sep_persistent; apply rfl_is_lock_pers.
    Qed.

    Lemma sgns_gt'_12 l1 s1
      (LVL1 : l1 ∈ rfl_lvls RFL1):
      sgn s1 l1 None -∗ sgns_levels_gt' {[s1]} (rfl_lvls RFL2).
    Proof using LOCKS_ORDER CL.
      clear dependent d__cl. 
      iIntros "#SGN". 
      iApply big_opS_singleton. iExists _. iFrame "#∗".
      iPureIntro. set_solver.
    Qed.

    Lemma acquire_two_spec τ π (lk1 lk2: val):
      {{{ two_locks lk1 lk2 ∗ 
          cp π d1 ∗ cp π d2 ∗ cp_mul π d__cl 5 ∗ th_phase_eq τ π ∗
          obls τ ∅          
      }}}
        acquire_two lk1 lk2 @ τ
      {{{ v, RET v; ∃ s1 s2 l1 l2, obls τ {[ s1; s2 ]} ∗ th_phase_eq τ π ∗ ⌜ s1 ≠ s2 ⌝ ∗
                          sgn s1 l1 None ∗ rfl_locked RFL1 s1 (rfl_G0 := RFLG1) ∗
                          sgn s2 l2 None ∗ rfl_locked RFL2 s2 (rfl_G0 := RFLG2) ∗ 
                          ⌜ l1 ∈ rfl_lvls RFL1 /\ l2 ∈ rfl_lvls RFL2 ⌝ }}}. 
    Proof using LOCKS_ORDER DEG2 DEG1 CL.
      iIntros (Φ) "(#LOCKS & CP1 & CP2 & CPS & PH & OB) POST". rewrite /acquire_two.
      pure_steps.
      iDestruct "LOCKS" as "[#LOCK1 #LOCK2]".
      wp_bind (rfl_acquire RFL1 lk1)%E.
      iApply (rfl_acquire_spec with "[-POST CPS CP2]").
      { iFrame "#∗". iApply empty_sgns_levels_rel. }
      iIntros "!> %v1 (%s1 & %l1 & OB & #SGN1 & %NEW1 & %LVL1 & PH & _ & L1)".
      wp_bind (Rec _ _ _)%E. pure_steps.
      rewrite union_empty_l_L. 
      iApply (rfl_acquire_spec with "[-POST L1]").
      { iFrame "#∗". by iApply sgns_gt'_12. }
      iIntros "!> %v2 (%s2 & %l2 & OB & #SGN2 & %NEW2 & %LVL2 & PH & _ & L2)".
      iApply "POST". iExists s1, s2. iFrame "#∗". 
      iPureIntro. set_solver. 
    Qed.

    Lemma release_two_spec τ π lk1 lk2 s1 s2 l1 l2 
      (NEQ: s1 ≠ s2):
      {{{ two_locks lk1 lk2 ∗ 
          cp π d1 ∗ cp π d2 ∗ cp_mul π d__cl 5 ∗ th_phase_eq τ π ∗
          obls τ {[ s1; s2 ]} ∗ sgn s1 l1 None ∗ sgn s2 l2 None ∗
          ⌜ l1 ∈ rfl_lvls RFL1 /\ l2 ∈ rfl_lvls RFL2 ⌝ ∗
          rfl_locked RFL1 s1 (rfl_G0 := RFLG1) ∗
          rfl_locked RFL2 s2 (rfl_G0 := RFLG2)
      }}}
        release_two lk1 lk2 @ τ
      {{{ v, RET v; obls τ ∅ ∗ th_phase_eq τ π }}}.
    Proof using LOCKS_ORDER DEG2 DEG1 CL.
      iIntros (Φ) "(#LOCKS & CP1 & CP2 & CPS & PH & OB & #SGN1 & #SGN2 & [%LVL1 %LVL2] & L1 & L2) POST". rewrite /release_two.
      pure_steps.
      iDestruct "LOCKS" as "[#LOCK1 #LOCK2]".

      wp_bind (rfl_release RFL2 lk2)%E.
      iApply (rfl_release_spec with "[-POST CPS CP1 L1]").
      2: iFrame "#∗".
      { set_solver. }
      { iSplitR; [iApply sgns_gt'_12| ]; eauto.
        iIntros "%q %Q PH OB". iModIntro. iSplit; [done| ].
        iIntros "PH'". iDestruct (th_phase_frag_combine' with "[$PH $PH']") as "foo"; [done| ].
        iAccu. }
      iIntros "!> %v2 [OB PH]".

      wp_bind (Rec _ _ _)%E. pure_steps.

      iApply (rfl_release_spec with "[-POST CPS]").
      2: iFrame "#∗".
      { apply not_elem_of_empty. }
      { iSplitR; [iApply empty_sgns_levels_rel| ].
        rewrite union_empty_l_L. iFrame.       
        iIntros "%q %Q PH OB". iModIntro. iSplit; [done| ].
        iIntros "PH'". iDestruct (th_phase_frag_combine' with "[$PH $PH']") as "foo"; [done| ].
        iAccu. }
      iIntros "!> %v1 [OB PH]".

      iApply "POST". iFrame.
    Qed. 
        
    Lemma thread_spec τ π (lk1 lk2: val):
      {{{ two_locks lk1 lk2 ∗ 
          cp_mul π d1 2 ∗ cp_mul π d2 2 ∗ cp_mul π d__cl 15 ∗ th_phase_eq τ π ∗
          obls τ ∅ }}}
        thread lk1 lk2 @ τ
      {{{ v, RET v; obls τ ∅ }}}.
    Proof using LOCKS_ORDER DEG2 DEG1 CL. 
      iIntros (Φ) "(#LOCKS & CP1 & CP2 & CPS & PH & OB) POST". rewrite /thread.
      split_cps "CP1" 1. split_cps "CP2" 1. 
      
      wp_bind (_%V lk1 lk2)%E.
      (* pure_steps. *)
      do 6 pure_step_cases.
      wp_bind (acquire_two lk1 lk2).
      split_cps "CPS" 5. 
      iApply (acquire_two_spec with "[-POST CP1' CP2' CPS]").
      { rewrite -!cp_mul_1. iFrame "#∗". }
      iIntros "!> %v1 (%s1 & %s2 & %l1 & %l2 & OB & PH & %NEQ & #SGN1 & L1 & #SGN2 & L2 & %LVLS)".

      wp_bind (Rec _ _ _)%E.
      do 3 pure_step_cases. 
      iApply (release_two_spec with "[-POST]").
      { eauto. }
      { rewrite -!cp_mul_1. by iFrame "#∗". }

      iIntros "!> %v [??]". by iApply "POST".
    Qed.

  End AfterInit. 

  Context {NO_OBS_POST: ∀ τ v, obls τ ∅ -∗ fork_post τ v}. 

  Context {CL_PRE: ClientPreG Σ} {FL_PRE1: rfl_preG RFL1 Σ} {FL_PRE2: rfl_preG RFL2 Σ}.

  Definition c__cl: nat := 0.
  Definition MAX_EXC := 6.
  Definition client_LB := max_list [MAX_EXC + 2; rfl_sb_fun RFL1 c__cl; rfl_sb_fun RFL2 c__cl].  
  Hypothesis (LS_LB: client_LB <= LIM_STEPS).

  Theorem client_spec τ π:
    {{{ obls τ ∅ ∗ th_phase_eq τ π ∗ cp_mul π d__cl 50 }}}
      client_two #() @ τ
    {{{ v, RET v; obls τ ∅ }}}.
  Proof using All.
    iIntros (Φ) "(OB & PH & CPS) POST". rewrite /client_two. 

    pure_step_hl. MU_by_BOU.
    iApply BOU_lower.
    { try_solve_bounds. use_rfl_fl_sb. }
    iApply BOU_split.
    split_cps "CPS" 1. rewrite -cp_mul_1.
    iApply (BOU_wand with "[-CPS']").
    2: { iApply (first_BOU with "[$]"). apply DEG1. }
    iIntros "(CPS1 & #EXC)".
    split_cps "CPS" 1.
    rewrite -cp_mul_1.
    iMod (exchange_cp_upd with "CPS' EXC") as "CPS2".
    { reflexivity. }
    { apply DEG2. }
    iModIntro. burn_cp_after_BOU.

    wp_bind (rfl_newlock _ _)%E.
    split_cps "CPS1" 1.
    iApply (rfl_newlock_spec with "[CPS1' PH]").
    { done. }
    { try_solve_bounds.
      unfold client_LB. simpl.
      etrans; [| apply Nat.le_max_r].
      apply Nat.le_max_l. }
    { rewrite -cp_mul_1. iFrame. iAccu. }
    iIntros "!> %lk1 (%RFL'1 & LOCK1 & PH)".

    wp_bind (Rec _ _ _)%E. pure_steps. 

    wp_bind (rfl_newlock _ _)%E.
    split_cps "CPS2" 1.
    iApply (rfl_newlock_spec with "[CPS2' PH]").
    { done. }
    { try_solve_bounds.
      unfold client_LB. simpl.
      do 2 (etrans; [| apply Nat.le_max_r]).
      apply Nat.le_max_l. }
    { rewrite -cp_mul_1. iFrame. iAccu. }
    iIntros "!> %lk2 (%RFL'2 & LOCK2 & PH)".

    wp_bind (Rec _ _ _)%E. pure_steps.

    pose proof (@two_locks_pers RFL'1 RFL'2 lk1 lk2) as PERS. 
    iAssert (two_locks lk1 lk2)%I with "[$LOCK1 $LOCK2]" as "#LOCKS".

    split_cps "CPS1" 2. split_cps "CPS2" 2. 

    wp_bind (Fork _)%E. 
    split_cps "CPS" 15.
    iApply sswp_MUf_wp. iIntros "%τ' !>".
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
    iApply (MU__f_wand with "[-CP PH OB]").
    2: { iApply ohe_obls_AMU__f; [done| ].
         iApply BOU_AMU__f.
         iApply BOU_intro. iFrame.
         iAccu. }
    iIntros "(_ & (%π1 & %π2 & PH1 & OB1 & PH2 & OB2 & [%PH_LT1 %PH_LT2]))".
    
    iSplitL "CPS1 CPS2 CPS' OB2 PH2".
    { iApply (thread_spec with "[-]").
      2: { iIntros "!> % OB". by iApply NO_OBS_POST. }
      rewrite intersection_empty_l_L. 
      apply strict_include in PH_LT2.
      do 3 (rewrite (cp_mul_weaken π); [| apply PH_LT2| reflexivity]).
      iFrame "#∗". }

    rewrite subseteq_empty_difference_L; [| done].

    iRename "PH1" into "PH".
    apply strict_include in PH_LT1.
    do 3 (rewrite (cp_mul_weaken π); [| apply PH_LT1| reflexivity]).
    clear dependent π. clear dependent π2. rename π1 into π. 

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (Fork _)%E. 
    split_cps "CPS" 15.
    iApply sswp_MUf_wp. iIntros "%τ'' !>".
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
    iApply (MU__f_wand with "[-CP PH OB1]").
    2: { iApply ohe_obls_AMU__f; [done| ].
         iApply BOU_AMU__f.
         iApply BOU_intro. iFrame.
         iAccu. }
    iIntros "(_ & (%π1 & %π2 & PH1 & OB1 & PH2 & OB2 & [%PH_LT1 %PH_LT2]))".
    
    iSplitL "CPS1' CPS2' CPS' OB2 PH2".
    { iApply (thread_spec with "[-]").
      2: { iIntros "!> % OB". by iApply NO_OBS_POST. }
      rewrite intersection_empty_l_L. 
      apply strict_include in PH_LT2.
      do 3 (rewrite (cp_mul_weaken π); [| apply PH_LT2| reflexivity]).
      iFrame "#∗". }

    iApply "POST".
    iApply obls_proper; [| done].
    symmetry. apply subseteq_empty_difference. done.
    Unshelve. all: done.
  Qed.

End MotivatingClient. 
