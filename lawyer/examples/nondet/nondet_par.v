From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From trillium.program_logic Require Export weakestpre ectx_lifting.
From fairness Require Import utils.
From lawyer.examples Require Import obls_tactics par.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


Class NondetPreG Σ := {
    nd_tok :: inG Σ (exclR unitO);
}.
Class NondetG Σ := {
    nd_pre :: NondetPreG Σ;
    γ__tok: gname;
}.


Section Nondet.
  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}. 

  Definition incr_loop: val :=
    rec: "loop" "c" "f" :=
      if: (!"f" = #true) then #()
      else (
        FAA "c" #1 ;;
        "loop" "c" "f"
      ).

  Definition get_cnt: val :=
    λ: "f" "c",
      "f" <- #true ;;
      !"c"
  .
  
  Context (l__f: Level).
  Context (d0 d1 d2: Degree).
  Hypotheses (DEG01: deg_lt d0 d1) (DEG12: deg_lt d1 d2).

  Definition tok `{NondetG Σ} := own γ__tok (Excl tt). 

  Context (K: nat).
  Hypothesis (K_LB: K <= LIM_STEPS).

  Definition nondet_inv_inner `{NondetG Σ} (cnt flag: loc) (s__f: SignalId): iProp Σ :=
    ∃ (c: nat) (f: bool), cnt ↦ #c ∗ flag ↦ #f ∗ sgn s__f l__f (Some f) ∗
                      (⌜ f = true ⌝ → tok) ∗
                       exc_lb (K * c). 

  Definition nondet_ns := nroot.@"nondet".
  Definition nondet_inv `{NondetG Σ} cnt flag s__f := inv nondet_ns (nondet_inv_inner cnt flag s__f).

  Context {NO_OBS_POST: ∀ τ v, obls τ ∅ -∗ fork_post τ v}.

  Definition nondet_LS_LB := 30. 
  Hypothesis (LS_LB: nondet_LS_LB <= LIM_STEPS).

  Lemma incr_loop_spec `{NondetG Σ} τ π cnt flag s__f:
    {{{ th_phase_eq τ π ∗ cp_mul π d0 10 ∗
        obls τ ∅ ∗ ep s__f π d0 ∗
        nondet_inv cnt flag s__f }}}
      incr_loop #cnt #flag @ τ
    {{{ v, RET v; obls τ ∅ ∗ th_phase_eq τ π }}}.
  Proof using LS_LB K_LB.
    iIntros (Φ) "(PH & CPS & OB & #EP & #INV) POST".
    iLöb as "IH". 
    rewrite /incr_loop.

    pure_steps.

    wp_bind (! _)%E.
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". iModIntro.
    rewrite {1}/nondet_inv_inner. iDestruct "inv" as ">(%c & %f & CNT & FLAG & SGN & TOK & #EB)".
    iApply sswp_MU_wp; [done| ]. iApply (wp_load with "[$]"). iIntros "!> FLAG".    

    destruct f. 
    1: { MU_by_burn_cp. iApply wp_value.
         iMod ("CLOS" with "[CNT SGN FLAG TOK]") as "_".
         { iNext. do 2 iExists _. iFrame "#∗". }
         iModIntro.
         
         wp_bind (_ = _)%E.
         iApply sswp_MU_wp; [done| ].
         iApply sswp_pure_step.
         { simpl. tauto. }
         MU_by_burn_cp.
         iApply wp_value. simpl. 
         pure_steps.
         iApply "POST". iFrame. }

    MU_by_BOU.
    iApply BOU_lower; [apply LS_LB| ]. iApply OU_BOU_rep.
    (* TODO: add proofmode class for OU_rep *)
    iPoseProof (expect_sig_upd_rep with "EP [$] [$] [] [$]") as "OU'".
    { iApply empty_sgns_levels_rel. }
    iApply (OU_rep_wand with "[-OU'] [$]").
    iIntros "(CPS' & SGN & OB & PH)".
    iCombine "CPS CPS'" as "CPS". rewrite -cp_mul_split.
    burn_cp_after_BOU.
    iApply wp_value. 
    iMod ("CLOS" with "[CNT FLAG SGN TOK]") as "_".
    { iNext. do 2 iExists _. iFrame "#∗". }
    iModIntro.
    
    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { simpl. tauto. }
    MU_by_burn_cp.
    
    pure_steps.
    
    wp_bind (FAA _ _)%E.
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". iModIntro.
    iClear "EB". clear c. 
    rewrite {1}/nondet_inv_inner. iDestruct "inv" as ">(%c & %f & CNT & FLAG & SGN & TOK & #EB)".
    iApply sswp_MU_wp; [done| ]. iApply (wp_faa with "[$]"). iIntros "!> CNT".
    
    MU_by_BOU.
    iApply BOU_lower; [apply K_LB| ]. iApply OU_BOU_rep.
    (* TODO: add proofmode instance *)
    iApply (OU_rep_wand with "[-]").
    2: { iApply (increase_eb_upd_rep with "EB"). }
    iIntros "#EB'". 
    burn_cp_after_BOU. iApply wp_value.
    
    iMod ("CLOS" with "[CNT FLAG SGN TOK]") as "_".
    { iNext. do 2 iExists _.
      replace (K * c + K) with (K * (c + 1)) by lia. 
      replace (Z.of_nat c + 1)%Z with (Z.of_nat (c + 1)) by lia.
      iFrame "#∗". }        
    iModIntro.
    
    wp_bind (Rec _ _ _)%E. do 3 pure_step_cases.
    iApply ("IH" with "[$] [CPS] [$] [$]").
    iApply (cp_mul_weaken with "[$]"); [done| ].
    rewrite /nondet_LS_LB. lia.       
  Qed.

  Lemma incr_loop_wrapper_spec `{NondetG Σ} τ π cnt flag s__f:
    {{{ th_phase_eq τ π ∗ cp π d2 ∗
        obls τ ∅ ∗ sgn s__f l__f None ∗
        nondet_inv cnt flag s__f }}}
      (λ: <>, incr_loop #cnt #flag)%V #() @ τ
    {{{ v, RET v; obls τ ∅ ∗ th_phase_eq τ π }}}.
  Proof using LS_LB K_LB DEG01 DEG12. 
    iIntros (Φ) "(PH & CP2 & OB & #SGN0 & #INV) POST".

    pure_step_hl. MU_by_BOU.
    iApply (BOU_lower _ (20 + 2)).
    { (* TODO: make abstract *)
      etrans; [| apply LS_LB].
      unfold nondet_LS_LB. lia. }
    iApply BOU_split. 
    iMod (first_BOU with "[$]") as "[CPS #EB]".
    { apply DEG12. }
    iModIntro. 
    split_cps "CPS" 1. rewrite -cp_mul_1. 
    iMod (create_ep_upd with "CPS' SGN0 PH") as "(#EP & _ & PH)".
    { eauto. }
    split_cps "CPS" 1. rewrite -cp_mul_1. 
    iMod (exchange_cp_upd with "CPS' EB") as "CPS0".
    { reflexivity. }
    { eauto. }
    BOU_burn_cp.

    iApply (incr_loop_spec with "[-POST]").
    2: done.
    iFrame "#∗".
    iApply (cp_mul_weaken with "CPS0"); [done| lia].
  Qed.

  Lemma alloc_nondet_inv `{NondetPreG Σ} τ cnt flag:
    cnt ↦ #(0%nat) -∗ flag ↦ #false -∗ obls τ ∅ -∗
    BOU ∅ 1 (∃ s__f (ND: NondetG Σ), nondet_inv cnt flag s__f ∗ obls τ {[ s__f ]} ∗ 
                                    sgn s__f l__f None ∗ tok).
  Proof using.
    iIntros "CNT FLAG OB".
    iMod (OU_create_sig _ _ l__f with "[$]") as "(%s__f & SGN & OB & _)".
    iDestruct (sgn_get_ex with "[$]") as "[SGN #SGN']".
    iMod (own_alloc (Excl tt: exclR unitO)) as (γ) "TOK".
    { done. }

    (* workaround to get exc_lb 0*)
    rewrite Nat.sub_diag. rewrite {2}(plus_n_O 0). iApply BOU_split.
    iApply OU_BOU_rep.
    iApply (OU_rep_wand with "[-]").
    2: { iApply (increase_eb_upd_rep0 0). }
    iIntros "EB".

    set (ND := {| γ__tok := γ |}).
    iMod (inv_alloc nondet_ns _ (nondet_inv_inner _ _ _) with "[-OB TOK]") as "#?".
    { do 2 iExists _. iNext. iFrame.
      rewrite Nat.mul_0_r. iFrame. by iIntros (?). } 

    iModIntro. do 2 iExists _. rewrite union_empty_l_L. iFrame "#∗".
  Qed.

  Lemma get_cnt_spec `{NondetG Σ} τ s__f flag cnt π F:
    {{{ nondet_inv cnt flag s__f ∗ obls τ ({[s__f]} ∪ F) ∗ tok ∗
        cp_mul π d0 10 ∗ th_phase_frag τ π 1 ∗ sgns_level_gt F l__f }}}
      get_cnt #flag #cnt @ τ
    {{{ (n: nat), RET #n; exc_lb (K * n) ∗ obls τ F ∗ th_phase_eq τ π }}}.
  Proof using NO_OBS_POST LS_LB K_LB DEG01.
    clear DEG12.
    iIntros (Φ) "(#INV & OB1 & TOK & CPS & PH & #SGNS_GT) POST".
    rewrite /get_cnt. pure_steps.
    
    wp_bind (_ <- _)%E.
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". iModIntro.
    rewrite {1}/nondet_inv_inner. iDestruct "inv" as ">(%c & %f & CNT & FLAG & SGN & TOK' & EXc)".
    iApply sswp_MU_wp; [done| ]. iApply (wp_store with "[$]"). iIntros "!> FLAG".
    MU_by_BOU.
    iDestruct (sgn_get_ex with "[$]") as "[SGN #SGN0]". 
    iMod (OU_set_sig with "OB1 [$]") as "[SGN OB]".
    { set_solver. }
    { unfold nondet_LS_LB in LS_LB. lia. }
    BOU_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[CNT FLAG SGN TOK TOK' EXc]") as "_".
    { iExists _, true. iNext. iFrame. done. }
    iModIntro. 
    
    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (! _)%E. 
    clear c f. 
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". iModIntro.
    rewrite {1}/nondet_inv_inner. iDestruct "inv" as ">(%c & %f & CNT & FLAG & SGN & TOK & #EXc)".
    iApply sswp_MU_wp; [done| ]. iApply (wp_load with "CNT"). iIntros "!> CNT".
    MU_by_burn_cp. iApply wp_value. 
    iMod ("CLOS" with "[CNT FLAG SGN TOK]") as "_".
    { do 2 iExists _. iFrame "#∗". }
    iModIntro.

    iApply "POST". iFrame "#∗".
    iAssert (⌜ s__f ∉ F ⌝)%I as %NIN.
    { destruct (decide (s__f ∈ F)); [| done].
      iDestruct (sgns_levels_rel_irrefl with "SGNS_GT [$]") as %NIN; set_solver. }
    iApply (obls_proper with "[$]"). set_solver.
  Qed.

  Lemma get_cnt_wrapper_spec `{NondetG Σ} τ s__f flag cnt π F:
    {{{ nondet_inv cnt flag s__f ∗ obls τ ({[s__f]} ∪ F) ∗ tok ∗
        cp π d1 ∗ th_phase_frag τ π 1 ∗ sgns_level_gt F l__f }}}
      (λ: <>, get_cnt #flag #cnt)%V #() @ τ
    {{{ (n: nat), RET #n; exc_lb (K * n) ∗ obls τ F ∗ th_phase_eq τ π }}}.
  Proof using NO_OBS_POST LS_LB K_LB DEG01.
    iIntros (Φ) "(#INV & OB1 & TOK & CP1 & PH & #SGNS_GT) POST".

    pure_step_hl. MU_by_BOU. 
    iMod (first_BOU with "[$]") as "[CPS #EB]".
    { apply DEG01. }
    BOU_burn_cp. 

    iApply (get_cnt_spec with "[-POST]").
    2: done.
    iFrame "#∗".
    iApply (cp_mul_weaken with "[$]"); [done| lia].
  Qed. 

  Context (l__w: Level).
  Hypothesis (LTfw: lvl_lt l__f l__w).
  
  Lemma get_cnt_spawnee_spec `{NondetG Σ} s__f flag cnt:
    nondet_inv cnt flag s__f ∗ tok ⊢
    spawnee_spec l__f (App (λ: <>, get_cnt #flag #cnt)%V #()) {[s__f]} d1
                (fun (vn: val) => (∃ (n: nat), ⌜ vn = #n ⌝ ∗ exc_lb (K * n))%I).
  Proof using NO_OBS_POST LS_LB K_LB DEG01.
    rewrite /spawnee_spec. iIntros "(#INV & TOK) %F %τ %π OB #SGNS_GT PH CP".
    iApply (get_cnt_wrapper_spec with "[-]"). 
    { iFrame "#∗". }
    iIntros "!> %n (?&?&?)".
    iExists _. iFrame. done. 
  Qed.

  Lemma incr_loop_waiter_spec `{NondetG Σ} s__f flag cnt:
    nondet_inv cnt flag s__f ∗ sgn s__f l__f None ⊢ waiter_spec (App (λ: <>, incr_loop #cnt #flag)%V #()) ∅ ∅ d2
                (fun (vn: val) => True%I).
  Proof using LS_LB K_LB DEG12 DEG01.
    rewrite /waiter_spec. iIntros "(#INV & #SGN0) %τ %π OB PH CP".
    iApply (incr_loop_wrapper_spec with "[-]").
    { iFrame "#∗". }
    iIntros "!> % (?&?)".
    iExists _. by iFrame.
  Qed.

  Definition nondet_par: val :=
    λ: <>,
      let: "c" := ref #(0%nat) in
      let: "f" := ref #false in
      Fst (par (λ: <>, get_cnt "f" "c") (λ: <>, incr_loop "c" "f"))      
  .

  Theorem nondet_par_spec `{NondetPreG Σ, parG Σ} τ π:
    {{{ th_phase_eq τ π ∗ cp_mul π d2 3 ∗ obls τ ∅ }}}
      nondet_par #() @ τ
    {{{ (n: nat), RET #n; ∃ π', exc_lb (K * n) ∗ obls τ ∅ ∗
                                th_phase_eq τ π' ∗ ⌜ phase_le π π' ⌝}}}.
  Proof.
    iIntros (Φ) "(PH & CPS2 & OB) POST". rewrite /nondet_par.

    split_cps "CPS2" 1. rewrite -cp_mul_1.
    pure_step_hl. MU_by_BOU.
    iMod (first_BOU with "[$]") as "[CPS #EB]".
    { eauto. }
    BOU_burn_cp.

    wp_bind (ref _)%E.
    iApply sswp_MU_wp; [done| ]. iApply wp_alloc. iIntros "!> %cnt CNT _".
    MU_by_burn_cp. iApply wp_value.

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (ref _)%E.
    iApply sswp_MU_wp; [done| ]. iApply wp_alloc. iIntros "!> %flag FLAG _".
    MU_by_BOU.
    iApply (BOU_weaken ∅); [reflexivity| set_solver| ..].
    { eauto. }
    iMod (alloc_nondet_inv with "[$] [$] [$]") as "(%s__f & %ND & #INV & OB & #SGN0 & TOK)".
    { unfold nondet_LS_LB in LS_LB. lia. }

    BOU_burn_cp. iApply wp_value.

    wp_bind (Rec _ _ _)%E.
    do 3 pure_step_cases. 

    wp_bind (Rec _ _ _)%E.
    do 2 pure_step_cases.
    wp_bind (Rec _ _ _)%E.
    do 2 pure_step_cases.

    wp_bind (par _ _)%E. 
    iClear "EB".
    split_cps "CPS" 1. 
    iApply (wp_wand with "[-POST CPS]").
    { split_cps "CPS2" 1. rewrite -!cp_mul_1.
      iApply (par_spec with "[] [TOK] [] [OB] [$] CPS2 CPS' CPS2'"). 
      { apply LTfw. }
      { apply DEG01. }
      { apply DEG12. }
      { (* TODO: abstract *)
        etrans; [| apply LS_LB].
        rewrite /par.fuels_spawn /nondet_LS_LB. lia. }
      { apply NO_OBS_POST. }
      2: { iApply incr_loop_waiter_spec. iFrame "#∗". }
      2: { iApply get_cnt_spawnee_spec. iFrame "#∗". }
      { set_solver. }
      all: cycle 1.
      { iApply (obls_proper with "[$]"). set_solver. }
      { iApply empty_sgns_levels_rel. }
      simpl. iIntros "!> %vw %vs OB _ (% & -> & EB) !>".
      Unshelve. 2: exact (fun (v: val) => (∃ (a: nat) (b: val), ⌜ v = PairV (#a) b⌝ ∗ obls τ ∅ ∗ exc_lb (K * a))%I).
      simpl. iExists _, _. iFrame. iPureIntro. reflexivity. }

    simpl. iIntros "% [(%n & % & -> & OB & EB) (% & PH & %PH_LE)]".
    rewrite cp_mul_weaken; eauto. pure_steps.
    iApply "POST". iExists _. iFrame "#∗". done.
  Qed.
  
End Nondet.
