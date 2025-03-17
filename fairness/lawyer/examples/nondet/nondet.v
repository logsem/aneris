From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From trillium.program_logic Require Export weakestpre ectx_lifting.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer.examples Require Import obls_tactics.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


Class NondetPreG Σ := {
    nd_tok :> inG Σ (exclR unitO);
}.
Class NondetG Σ := {
    nd_pre :> NondetPreG Σ;
    γ__tok: gname;
}.


Section Nondet.
  Context `{ODd: OfeDiscrete DegO} `{ODl: OfeDiscrete LevelO}.
  Context `{LEl: @LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}.
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.
  
  Let OAM := ObligationsAM.
  Let ASEM := ObligationsASEM.

  Context `{EM: ExecutionModel heap_lang M}.

  Context {Σ: gFunctors}.
  (* Keeping the more general interface for future developments *)
  Context `{oGS': @asem_GS _ _ ASEM Σ}.
  Let oGS: ObligationsGS (OP := OP) Σ := oGS'.
  Existing Instance oGS.

  Context `{hGS: @heapGS Σ _ EM}.
  Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).

  Definition incr_loop: val :=
    rec: "loop" "c" "f" :=
      if: (!"f" = #true) then #()
      else (
        FAA "c" #1 ;;
        "loop" "c" "f"
      ).
  
  Definition nondet: val :=
    λ: <>,
      let: "c" := ref #(0%nat) in
      let: "f" := ref #false in
      Fork (incr_loop "c" "f") ;;
      "f" <- #true ;;
      !"c"
  .

  Context (l__f: Level).
  Context (d0 d1: Degree).
  Hypotheses (DEG01: deg_lt d0 d1). 

  Definition tok `{NondetG Σ} := own γ__tok (Excl tt). 

  Context (K: nat).
  Hypothesis (K_LB: K <= LIM_STEPS).

  Definition nondet_inv_inner `{NondetG Σ} (cnt flag: loc) (s__f: SignalId): iProp Σ :=
    ∃ (c: nat) (f: bool), cnt ↦ #c ∗ flag ↦ #f ∗
                      (⌜ f = false ⌝ ∗ sgn s__f l__f (Some false) ∨ ⌜ f = true ⌝ ∗ tok) ∗
                      exc_lb (K * c). 

  Definition nondet_ns := nroot.@"nondet".
  Definition nondet_inv `{NondetG Σ} cnt flag s__f := inv nondet_ns (nondet_inv_inner cnt flag s__f).

  Context {OBLS_AMU: @AMU_lift_MU _ _ _ oGS' _ EM _ (↑ nroot)}.
  Context {OBLS_AMU__f: forall τ, @AMU_lift_MU__f _ _ _ τ oGS' _ EM _ ⊤}.
  Context {NO_OBS_POST: ∀ τ v, obls τ ∅ -∗ fork_post τ v}.

  Definition nondet_LS_LB := 30. 
  Hypothesis (LS_LB: nondet_LS_LB <= LIM_STEPS).

  Lemma incr_loop_spec `{NondetG Σ} τ π cnt flag s__f:
    {{{ th_phase_eq τ π ∗ cp_mul π d0 10 ∗
        obls τ ∅ ∗ ep s__f π d0 ∗
        nondet_inv cnt flag s__f }}}
      incr_loop #cnt #flag @ τ
    {{{ v, RET v; obls τ ∅ }}}.
  Proof using OBLS_AMU ODl LEl LS_LB K_LB.
    iIntros (Φ) "(PH & CPS & OB & #EP & #INV) POST".
    iLöb as "IH". 
    rewrite /incr_loop.

    pure_steps.

    wp_bind (! _)%E.
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". iModIntro.
    rewrite {1}/nondet_inv_inner. iDestruct "inv" as ">(%c & %f & CNT & FLAG & CASES & #EB)".
    iApply sswp_MU_wp; [done| ]. iApply (wp_load with "[$]"). iIntros "!> FLAG".
    

    iDestruct "CASES" as "[[-> SGN]| [-> TOK]]".
    2: { MU_by_burn_cp. iApply wp_value.
         iMod ("CLOS" with "[CNT FLAG TOK]") as "_".
         { iNext. do 2 iExists _. iFrame "#∗". iRight. by iFrame. }
         iModIntro.
         
         wp_bind (_ = _)%E.
         iApply sswp_MU_wp; [done| ].
         iApply sswp_pure_step.
         { simpl. tauto. }
         MU_by_burn_cp.
         iApply wp_value. simpl. 
         pure_steps.
         by iApply "POST". }

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
    iMod ("CLOS" with "[CNT FLAG SGN]") as "_".
    { iNext. do 2 iExists _. iFrame "#∗". iLeft. by iFrame. }
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
    rewrite {1}/nondet_inv_inner. iDestruct "inv" as ">(%c & %f & CNT & FLAG & CASES & #EB)".
    iApply sswp_MU_wp; [done| ]. iApply (wp_faa with "[$]"). iIntros "!> CNT".
    
    MU_by_BOU.
    iApply BOU_lower; [apply K_LB| ]. iApply OU_BOU_rep.
    (* TODO: add proofmode instance *)
    iApply (OU_rep_wand with "[-]").
    2: { iApply (increase_eb_upd_rep with "EB"). }
    iIntros "#EB'". 
    burn_cp_after_BOU. iApply wp_value.
    
    iMod ("CLOS" with "[CNT FLAG CASES]") as "_".
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

  Lemma alloc_nondet_inv `{NondetPreG Σ} τ cnt flag:
    cnt ↦ #(0%nat) -∗ flag ↦ #false -∗ obls τ ∅ -∗
    BOU ∅ 1 (∃ s__f (ND: NondetG Σ), nondet_inv cnt flag s__f ∗ 
                                    obls τ {[ s__f ]} ∗ sgn s__f l__f None ∗ tok).
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
      rewrite Nat.mul_0_r. iFrame. iLeft. by iFrame. }

    iModIntro. do 2 iExists _. rewrite union_empty_l_L. iFrame "#∗".
  Qed.

  Theorem nondet_spec `{NondetPreG Σ} τ π:
    {{{ th_phase_eq τ π ∗ cp_mul π d1 2 ∗ obls τ ∅ }}}
      nondet #() @ τ
    {{{ vn, RET vn; ∃ (n: nat) π', ⌜ vn = #n ⌝ ∗ exc_lb (K * n) ∗ 
                                  obls τ ∅ ∗ th_phase_eq τ π' ∗ ⌜ phase_le π π' ⌝}}}.
  Proof.
    iIntros (Φ) "(PH & CPS1 & OB) POST". rewrite /nondet.

    split_cps "CPS1" 1. rewrite -cp_mul_1.
    pure_step_hl. MU_by_BOU.
    iMod (first_BOU with "[$]") as "[CPS #EB]".
    { apply DEG01. }
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
    iMod (create_ep_upd with "[$] [$] [$]") as "(#EP & _ & PH)".
    { apply DEG01. }
    { unfold nondet_LS_LB in LS_LB. lia. }
    BOU_burn_cp. iApply wp_value.

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (Fork _)%E.
    iApply sswp_MUf_wp. iIntros (τ') "!>".
    split_cps "CPS" 1.

    MU__f_by_BOU (∅: gset SignalId). 
    iModIntro. iSplitR "CPS' PH OB". 
    2: { iExists _. rewrite cp_mul_1. by iFrame. }
    iIntros "(%π1 & %π2 & PH1 & OB1 & PH2 & OB2 & [%PH_LT1 %PH_LT2])".

    split_cps "CPS" 10. 
    iSplitR "CPS PH1 OB1 POST TOK".
    { erewrite ep_weaken; [| apply PH_LT2].
      erewrite cp_mul_weaken; [| apply PH_LT2| reflexivity].
      rewrite intersection_empty_r_L.
      iApply (incr_loop_spec with "[-]").
      { iFrame "#∗". }
      iIntros "!> % OB". by iApply NO_OBS_POST. }

    erewrite cp_mul_weaken; [| apply PH_LT1| reflexivity]. iRename "PH1" into "PH".
    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (_ <- _)%E.
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". iModIntro.
    rewrite {1}/nondet_inv_inner. iDestruct "inv" as ">(%c & %f & CNT & FLAG & CASES & EXc)".
    iDestruct "CASES" as "[[-> SGN] | [-> TOK']]".
    2: { iCombine "TOK TOK'" as "TOK". by iDestruct (own_valid with "TOK") as %V. }
    iApply sswp_MU_wp; [done| ]. iApply (wp_store with "[$]"). iIntros "!> FLAG".
    MU_by_BOU.
    iMod (OU_set_sig with "[$] [$]") as "[SGN OB]".
    { set_solver. }
    { unfold nondet_LS_LB in LS_LB. lia. }
    BOU_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[CNT FLAG TOK EXc]") as "_".
    { do 2 iExists _. iFrame. iNext. iRight. by iFrame. }
    iModIntro. 
    
    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (! _)%E. 
    clear c. 
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". iModIntro.
    rewrite {1}/nondet_inv_inner. iDestruct "inv" as ">(%c & %f & CNT & FLAG & CASES & #EXc)".
    iApply sswp_MU_wp; [done| ]. iApply (wp_load with "CNT"). iIntros "!> CNT".
    MU_by_burn_cp. iApply wp_value. 
    iMod ("CLOS" with "[CNT FLAG CASES]") as "_".
    { do 2 iExists _. iFrame "#∗". }
    iModIntro.

    iApply "POST". do 2 iExists _. iFrame "#∗". iSplit; [done| ].
    iSplit; [| iPureIntro; by apply PH_LT1]. 
    iApply (obls_proper with "[$]"). set_solver.
  Qed.
  
End Nondet.
