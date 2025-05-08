From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From trillium.program_logic Require Export weakestpre ectx_lifting.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer.examples Require Import obls_tactics.
From trillium.fairness.lawyer.examples.nondet Require Import nondet.
From trillium.fairness.lawyer.examples.const_term Require Import const_term.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From trillium.fairness.lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


Section RTBound.
  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}. 

  Definition rt_bound: val :=
    λ: <>,
      let: "n" := nondet #() in
      let: "l" := ref "n" in
      decr "l"
  .

  Context (l__f: Level).
  Context (d0 d1: Degree).
  Hypotheses (DEG01: deg_lt d0 d1). 

  Context {NO_OBS_POST: ∀ τ v, obls τ ∅ -∗ fork_post τ v}.

  Hypothesis (ND_LB_LS: nondet_LS_LB <= LIM_STEPS).

  Definition DECR_ITER_LEN := 10.

  Hypothesis (DIL_LS: S DECR_ITER_LEN <= LIM_STEPS).

  Lemma rt_bound_spec `{NondetPreG Σ, DecrPreG Σ} τ π:
    {{{ th_phase_eq τ π ∗ cp_mul π d1 5 ∗ obls τ ∅ }}}
      rt_bound #() @ τ
    {{{ v, RET v; obls τ ∅ }}}.
  Proof.
    iIntros (Φ) "(PH & CPS1 & OB) POST". rewrite /rt_bound.

    split_cps "CPS1" 1. rewrite -cp_mul_1.
    pure_step_hl. MU_by_BOU.
    iMod (first_BOU with "[$]") as "[CPS #EB]".
    { apply DEG01. }
    BOU_burn_cp.

    split_cps "CPS1" 2. 
    wp_bind (nondet _)%E.
    iApply (nondet_spec with "[$CPS1 $PH $OB]").
    { exact l__f. }
    { apply DEG01. }
    { apply DIL_LS. }
    1-2: by eauto.
    iIntros "!> %v (%n & %π' & -> & #EBn & OB & PH & %PH_LE)".
    rewrite cp_mul_weaken; [| apply PH_LE| reflexivity].

    wp_bind (Rec _ _ _)%E. rewrite Nat.mul_comm. pure_steps.

    wp_bind (ref _)%E.
    iApply sswp_MU_wp; [done| ]. iApply wp_alloc. iIntros "!> %l L _".
    (* TODO: why elimination takes so long? *)
    iMod (alloc_decr_inv with "L") as (?) "[#DECR_INV CNT]".     
    MU_by_burn_cp. iApply wp_value.

    split_cps "CPS1'" 1. rewrite -cp_mul_1.  
    wp_bind (Rec _ _ _)%E.
    pure_step_hl. MU_by_BOU.
    iMod (exchange_cp_upd with "CPS1' EBn") as "CPS'".
    { reflexivity. }
    { apply DEG01. }
    { unfold DECR_ITER_LEN in DIL_LS. lia. }
    iMod (exchange_cp_upd with "CPS1'' EB") as "CPS''".
    { reflexivity. }
    { apply DEG01. }
    { unfold DECR_ITER_LEN in DIL_LS. lia. }    
    BOU_burn_cp. iApply wp_value.
    
    pure_steps.

    iCombine "CPS' CPS''" as "CPSd". rewrite -cp_mul_split.
    iApply (decr_spec with "[$PH $DECR_INV $CNT CPSd]").
    { iApply (cp_mul_weaken with "[$]"); [done| ].
      rewrite /DECR_ITER_LEN. lia. }
    iIntros "!> % _". by iApply "POST".
  Qed.

End RTBound.
