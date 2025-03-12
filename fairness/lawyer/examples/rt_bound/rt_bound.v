From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From trillium.program_logic Require Export weakestpre ectx_lifting.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer.examples Require Import obls_tactics.
From trillium.fairness.lawyer.examples.nondet Require Import nondet.
From trillium.fairness.lawyer.examples.const_term Require Import const_term.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


Section RTBound.
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

  Definition rt_bound: val :=
    λ: <>,
      let: "n" := nondet #() in
      let: "l" := ref "n" in
      decr "l"
  .

  Context (l__f: Level).
  Context (d0 d1: Degree).
  Hypotheses (DEG01: deg_lt d0 d1). 

  Context {OBLS_AMU: @AMU_lift_MU _ _ _ oGS' _ EM _ (↑ nroot)}.
  Context {OBLS_AMU__f: forall τ, @AMU_lift_MU__f _ _ _ τ oGS' _ EM _ ⊤}.
  Context {NO_OBS_POST: ∀ τ v, obls τ ∅ -∗ fork_post τ v}.

  Hypothesis (ND_LB_LS: nondet_LS_LB <= LIM_STEPS). 

  Lemma rt_bound_spec `{NondetPreG Σ, DecrPreG} τ π:
    {{{ th_phase_eq τ π ∗ cp_mul π d1 4 ∗ obls τ ∅ }}}
      rt_bound #() @ τ
    {{{ v, RET v; obls τ ∅ }}}.
  Proof using OBLS_AMU.
    iIntros (Φ) "(PH & CPS1 & OB) POST". rewrite /rt_bound.

    split_cps "CPS1" 1. rewrite -cp_mul_1.
    pure_step_hl. MU_by_BOU.
    iMod (first_BOU with "[$]") as "[CPS #EB]".
    { apply DEG01. }
    BOU_burn_cp.

    split_cps "CPS1" 1. rewrite -cp_mul_1.
    wp_bind (nondet _)%E.
    iApply (nondet_spec with "[$CPS1 $PH $OB]").
    { exact l__f. }
    { apply DEG01. }
    1-4: by eauto.
    iIntros "!> %v (%n & %π' & -> & #EBn & OB & PH & %PH_LE)".
    rewrite cp_mul_weaken; [| apply PH_LE| reflexivity].

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (ref _)%E.
    iApply sswp_MU_wp; [done| ]. iApply wp_alloc. iIntros "!> %l L _".
    (* TODO: why elimination takes so long? *)
    iMod (alloc_decr_inv with "L") as (?) "[#DECR_INV CNT]".     
    MU_by_burn_cp. iApply wp_value.

    wp_bind (Rec _ _ _)%E.
    pure_step_hl. MU_by_BOU.
    iMod (first_BOU with "[$]") as "[CPS #EB]".
    { apply DEG01. }
    BOU_burn_cp.
    
    pure_steps.

    

    
    



End RTBound.
