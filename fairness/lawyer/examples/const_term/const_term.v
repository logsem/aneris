From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer.examples Require Import signal_map obls_tactics.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em program_logic.
From trillium.fairness.lawyer.examples.ticketlock Require Import obls_atomic fair_lock.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


Section Decr.
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

  Definition decr: val :=
    rec: "decr" "l" :=
      let: "c" := !"l" in
      if: ("c" = #0) then #()
      else ("l" <- "c" - #1 ;; "decr" "l")
    .

  Context {OBLS_AMU: @AMU_lift_MU _ _ _ oGS' _ EM _ (↑ nroot)}.
  Context {OBLS_AMU__f: forall τ, @AMU_lift_MU__f _ _ _ τ oGS' _ EM _ ⊤}.
  Context {NO_OBS_POST: ∀ τ v, obls τ ∅ -∗ fork_post τ v}. 

  Lemma decr_spec τ π d l (N: nat):
    {{{ th_phase_eq τ π ∗ cp_mul π d ((N + 1) * 10) ∗
        l ↦ #N }}}
      decr #l @ τ
    {{{ v, RET v; ⌜ True ⌝ }}}.
  Proof using OBLS_AMU.
    iIntros (Φ) "(PH & CPS & L) POST".
    iLöb as "IH" forall (N). 
    rewrite /decr.
    rewrite Nat.mul_add_distr_r Nat.mul_1_l.
    iDestruct (cp_mul_split with "CPS") as "[CPS' CPS]".

    pure_steps.

    wp_bind (! _)%E.
    iApply sswp_MU_wp; [done| ]. iApply (wp_load with "[$]"). iIntros "!> L".
    MU_by_burn_cp.
    
    pure_steps. wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { simpl. tauto. }
    MU_by_burn_cp.
    iApply wp_value.

    destruct N.
    { simpl. pure_steps. by iApply "POST". }
    rewrite -{1}(Nat.add_1_r N). simpl. pure_steps.

    wp_bind (_ - _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { simpl. tauto. }
    MU_by_burn_cp.
    iApply wp_value.

    wp_bind (_ <- _)%E.
    iApply sswp_MU_wp; [done| ]. iApply (wp_store with "[$]"). iIntros "!> L".
    MU_by_burn_cp.
    iApply wp_value.

    wp_bind (Rec _ _ _)%E. do 1 pure_step_cases.
    iApply wp_value.
    pure_step.

    (* Set Printing Coercions. *)
    replace (Z.of_nat (S N) - 1)%Z with (Z.of_nat N) by lia. 
    iApply ("IH" with "[$] [$] [$] [$]").
  Qed.


  (* TODO: move? *)

  Context (N: nat).
      
  Definition const_term: val :=
    λ: <>, 
      let: "l" := ref #N in
      (Fork (decr "l") ;;
       !"l")
    .


  Lemma const_term_spec τ π d:
    {{{ th_phase_eq τ π ∗ cp_mul π d ((N + 2) * 10) ∗ obls τ ∅ }}}
      const_term #()  @ τ
    {{{ v, RET v; obls τ ∅ }}}.
  Proof using. 
    iIntros (Φ) "(PH & CPS & OB) POST".
    rewrite Nat.mul_add_distr_r. simpl. 
    iDestruct (cp_mul_split with "CPS") as "[CPS' CPS]".
    rewrite /const_term.

    pure_steps.

    wp_bind (ref _)%E.
    iApply sswp_MU_wp; [done| ]. iApply wp_alloc. iIntros "!> %l L _".
Ltac MU_by_BOU :=
  match goal with
  | [OB_AMU: AMU_lift_MU _ _ _ _ _ |- envs_entails _ (MU _ _ _) ] =>
      iApply OB_AMU; [by rewrite nclose_nroot| ];
      iApply BOU_AMU
  | [OBLS_AMU__f: forall τ, @AMU_lift_MU__f _ _ _ _ _ _ _ _ _ |-
                       envs_entails _ (MU__f _ _ _ _) ] =>
      iApply OBLS_AMU__f 
      (* [| iApply BOU_AMU__f] *)
  end. 
Ltac MU_by_burn_cp := MU_by_BOU; BOU_burn_cp.

    MU_by_burn_cp.
    iApply wp_value. 
    
    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (Fork _)%E.
    iApply sswp_MUf_wp. iIntros (τ') "!>".
    (* MU_by_burn_cp.  *)
    MU_by_BOU.
    2: {
      iApply BOU_AMU__f. 


    

  
End Decr.
