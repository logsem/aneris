From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From trillium.program_logic Require Export weakestpre ectx_lifting.
From fairness Require Import utils.
From lawyer.examples Require Import obls_tactics.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


Class DecrPreG Σ := {
    decr_cnt :> inG Σ (excl_authUR natO);
}.
Class DecrG Σ := {
    decr_pre :> DecrPreG Σ;
    γ__decr: gname;
}.


Section Decr.
  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}. 

  Definition decr: val :=
    rec: "decr" "l" :=
      let: "c" := !"l" in
      if: ("c" = #0) then #()
      else ("l" <- "c" - #1 ;; "decr" "l")
    .

  Definition cnt_auth `{DecrG Σ} (n: nat) :=
    own γ__decr (● (Excl' n)). 
  Definition cnt_frag `{DecrG Σ} (n: nat) :=
    own γ__decr (◯ (Excl' n)). 

  (* TODO: these lemmas are used way too often, move them to library *)
  Lemma cnt_agree `{DecrG Σ} n1 n2:
    cnt_auth n1-∗ cnt_frag n2 -∗ ⌜ n1 = n2 ⌝.
  Proof using.
    rewrite /cnt_frag /cnt_auth.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
      iPureIntro. apply excl_auth_agree_L in Hval. set_solver.
  Qed.
  
  Lemma cnt_update `{DecrG Σ} n1 n2 n':
    cnt_auth n1 -∗ cnt_frag n2 ==∗
      cnt_auth n' ∗ cnt_frag n'.
  Proof using.
    rewrite /cnt_frag /cnt_auth.
    iIntros "HA HB". iCombine "HB HA" as "H".
    rewrite -!own_op. iApply own_update; [| by iFrame].
    apply excl_auth_update.
  Qed.

  Definition decr_inv_inner `{DecrG Σ} (l: loc): iProp Σ :=
    ∃ (n: nat), l ↦ #n ∗ cnt_auth n.

  Definition decr_ns := nroot.@"decr".
  Definition decr_inv `{DecrG Σ} l := inv decr_ns (decr_inv_inner l).

  Context {NO_OBS_POST: ∀ τ v, obls τ ∅ -∗ fork_post τ v}. 

  Lemma decr_spec `{DecrG Σ} τ π d l (N: nat):
    {{{ th_phase_eq τ π ∗ cp_mul π d ((N + 1) * 10) ∗
        decr_inv l ∗ cnt_frag N }}}
      decr #l @ τ
    {{{ v, RET v; ⌜ True ⌝ }}}.
  Proof using.
    iIntros (Φ) "(PH & CPS & #INV & CNT) POST".
    iLöb as "IH" forall (N). 
    rewrite /decr.
    rewrite Nat.mul_add_distr_r Nat.mul_1_l.
    iDestruct (cp_mul_split with "CPS") as "[CPS' CPS]".

    pure_steps.

    wp_bind (! _)%E.
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". iModIntro.
    rewrite {1}/decr_inv_inner. iDestruct "inv" as ">(%n & L & AUTH)".
    iDestruct (cnt_agree with "[$] [$]") as %->.     
    iApply sswp_MU_wp; [done| ]. iApply (wp_load with "[$]"). iIntros "!> L".
    MU_by_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[AUTH L]") as "_".
    { iExists _. iFrame. }
    iModIntro. 
    
    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { simpl. tauto. }
    MU_by_burn_cp.
    iApply wp_value.

    destruct N.
    { simpl. pure_steps. by iApply "POST". }
    rewrite -{2}(Nat.add_1_r N). simpl. pure_steps.

    wp_bind (_ - _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { simpl. tauto. }
    MU_by_burn_cp.
    iApply wp_value.
    replace (Z.of_nat (S N) - 1)%Z with (Z.of_nat N) by lia. 

    wp_bind (_ <- _)%E.
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". iModIntro.
    rewrite {1}/decr_inv_inner. iDestruct "inv" as ">(%n & L & AUTH)".
    iDestruct (cnt_agree with "[$] [$]") as %->.
    iApply sswp_MU_wp; [done| ]. iApply (wp_store with "[$]"). iIntros "!> L".
    MU_by_BOU.    
    iMod (cnt_update _ _ N with "[$] [$]") as "[AUTH CNT]".
    BOU_burn_cp. iApply wp_value. 
    iMod ("CLOS" with "[AUTH L]") as "_".
    { iExists _. iFrame. }
    iModIntro. 

    wp_bind (Rec _ _ _)%E. do 1 pure_step_cases.
    iApply wp_value.
    pure_step.

    iApply ("IH" with "[$] [$] [$] [$]").
  Qed.


  Context (N: nat).
      
  Definition const_term: val :=
    λ: <>, 
      let: "l" := ref #N in
      (Fork (decr "l") ;;
       !"l")
    .

  Lemma alloc_decr_inv `{DecrPreG Σ} l (n: nat):
    l ↦ #n ={∅}=∗ ∃ (D: DecrG Σ), decr_inv l ∗ cnt_frag n.
  Proof using.
    iIntros "L".
    iMod (own_alloc ((● Excl' n ⋅ ◯ _): excl_authUR natO)) as (γ) "[AUTH ?]".
    { apply auth_both_valid_2; [| reflexivity]. done. }
    set (D := {| γ__decr := γ |}). 
    iMod (inv_alloc decr_ns _ (decr_inv_inner l) with "[L AUTH]") as "#?".
    { iExists _. iNext. iFrame. }
    iModIntro. iExists _.  iFrame "#". 
    rewrite /cnt_frag. simpl. subst D. iFrame.
  Qed.

  Lemma const_term_spec `{DecrPreG Σ} τ π d:
    {{{ th_phase_eq τ π ∗ cp_mul π d ((N + 2) * 10) ∗ obls τ ∅ }}}
      const_term #() @ τ
    {{{ v, RET v; obls τ ∅ }}}.
  Proof using NO_OBS_POST.
    iIntros (Φ) "(PH & CPS & OB) POST".

    replace (N + 2) with (N + 1 + 1) by lia.
    rewrite Nat.mul_add_distr_r. simpl. 
    iDestruct (cp_mul_split with "CPS") as "[CPSd CPS]".
    rewrite /const_term.

    pure_steps.

    wp_bind (ref _)%E.
    iApply sswp_MU_wp; [done| ]. iApply wp_alloc. iIntros "!> %l L _".
    (* TODO: why elimination takes so long? *)
    iMod (alloc_decr_inv with "L") as (?) "[#INV CNT]". 
    
    MU_by_burn_cp. iApply wp_value. 
    
    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (Fork _)%E.
    iApply sswp_MUf_wp. iIntros (τ') "!>".
    split_cps "CPS" 1.

    MU__f_by_BOU (∅: gset SignalId). 
    iModIntro. iSplitR "CPS' PH OB". 
    2: { iExists _. rewrite cp_mul_1. by iFrame. }
    iIntros "(%π1 & %π2 & PH1 & OB1 & PH2 & OB2 & [%PH_LT1 %PH_LT2])".

    iSplitL "CPSd PH2 CNT OB2".
    - rewrite cp_mul_weaken; [..| reflexivity]. 
      2: { apply PH_LT2. }
      iApply (decr_spec with "[-OB2]").
      { iFrame "#∗". }
      iNext. iIntros. iApply NO_OBS_POST.
      iApply (obls_proper with "[$]"). symmetry. set_solver.
    - rewrite difference_diag_L.
      rewrite cp_mul_weaken; [.. | reflexivity].
      2: { apply PH_LT1. }
      iRename "PH1" into "PH".
      wp_bind (Rec _ _ _)%E. pure_steps.

      iApply wp_atomic.
      iInv "INV" as "inv" "CLOS". iModIntro.
      rewrite {1}/decr_inv_inner. iDestruct "inv" as ">(%n & L & AUTH)".
      iApply sswp_MU_wp; [done| ]. iApply (wp_load with "[$]"). iIntros "!> L".
      MU_by_BOU.    
      BOU_burn_cp. iApply wp_value. 
      iMod ("CLOS" with "[AUTH L]") as "_".
      { iExists _. iFrame. }
      iModIntro. by iApply "POST".
  Qed.
  
End Decr.
