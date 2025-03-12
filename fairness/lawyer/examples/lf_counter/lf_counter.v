From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From trillium.program_logic Require Export weakestpre ectx_lifting.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer.examples Require Import obls_tactics.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


Class LFCPreG Σ := {
    lfc_wm :> inG Σ (authUR (gmapUR nat natUR));
}.


Class LFCG Σ := {
    lfc_pre :> LFCPreG Σ;
    γ__wm: gname;
}.


Section WaitMap.
  Context `{LFCG Σ}.

  Definition wm_auth (wm: gmap nat nat) :=
    own γ__wm ((● wm): authUR (gmapUR nat natUR)). 

  Definition val_toks (i k: nat) :=
    own γ__wm ((◯ {[ i := k ]}): authUR (gmapUR nat natUR)).

  Definition val_tok (i: nat) := val_toks i 1. 

  Lemma wm_auth_toks_ge wm i k:
    wm_auth wm -∗ val_toks i k -∗ ⌜ exists n, wm !! i = Some n /\ k <= n ⌝.
  Proof using.
    iApply bi.wand_curry. rewrite -own_op. 
    iIntros "X". iDestruct (own_valid with "X") as %V. iPureIntro.
    apply auth_both_valid_discrete in V as [SUB V].
    apply singleton_included_l in SUB as (? & ITH & LE).
    apply leibniz_equiv_iff in ITH. eexists. split; eauto.
    rewrite Some_included_total in LE.
    by apply nat_included.
  Qed.

  Lemma wm_alloc wm i:
    wm_auth wm ==∗ wm_auth (<[ i := default 0 (wm !! i) + 1 ]> wm) ∗ val_tok i.
  Proof using.
    iIntros "WM". rewrite -own_op. rewrite /wm_auth.
    iApply (own_update with "[$]"). apply auth_update_alloc.
    destruct (wm !! i) eqn:ITH; simpl.
    - eapply insert_alloc_local_update; eauto.
      apply nat_local_update.
      set_solver.
    - apply alloc_local_update; eauto. done.
  Qed.  

End WaitMap.


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

  Context (d0 d1: Degree).
  Hypotheses (DEG01: deg_lt d0 d1). 

  (* Context (K: nat). *)
  (* Hypothesis (K_LB: K <= LIM_STEPS). *)

  Definition INCR_ITER_LEN := 10.
  Hypothesis (INCR_LS_LB: 2 + INCR_ITER_LEN <= LIM_STEPS).

  Local Instance filter_key_dec c:
    ∀ x : nat * nat, Decision ((gt c ∘ fst) x).
  Proof using.
    intros [??]. simpl. rewrite /gt. solve_decision.
  Qed.

  Definition wm_interp `{LFCG Σ} π0 c (wm: gmap nat nat): iProp Σ :=
    [∗ map] i ↦ n ∈ filter (gt c ∘ fst) wm, 
      (∃ r, cp π0 d0 ∨ val_toks i (n - r)).

  Definition wm_eb (wm: gmap nat nat): iProp Σ :=
    exc_lb $ list_max $ elements $ (map_img wm: gset nat). 

  Definition cnt_inv_inner `{LFCG Σ} (cnt: loc) (π0: Phase): iProp Σ :=
    ∃ (c: nat) wm, cnt ↦ #c ∗ wm_auth wm ∗ wm_interp π0 c wm ∗ wm_eb wm. 

  Definition cnt_ns := nroot.@"cnt".
  Definition cnt_inv `{LFCG Σ} cnt π0 := inv cnt_ns (cnt_inv_inner cnt π0).

  Context {OBLS_AMU: @AMU_lift_MU _ _ _ oGS' _ EM _ (↑ nroot)}.
  Context {OBLS_AMU__f: forall τ, @AMU_lift_MU__f _ _ _ τ oGS' _ EM _ ⊤}.
  Context {NO_OBS_POST: ∀ τ v, obls τ ∅ -∗ fork_post τ v}.

  Definition incr_impl: val :=
    rec: "incr_impl" "c" :=
      let: "n" := !"c" in
      if: CAS "c" "n" ("n" + #1) then #()
      else "incr_impl" "c"
  . 

  Definition incr: val :=
    λ: "c", incr_impl "c". 

  Lemma incr_impl_spec `{LFCG Σ} τ π cnt π0
    (PH: phase_le π0 π):
    {{{ cnt_inv cnt π0 ∗ exc_lb (S INCR_ITER_LEN) ∗ 
        cp π0 d1 ∗ cp_mul π d0 INCR_ITER_LEN ∗ 
        th_phase_frag τ π 1 }}}
      incr_impl #cnt @τ
    {{{ v, RET v; ⌜ True ⌝ }}}.
  Proof using.
    iIntros (Φ) "(#INV & #EB & CP1 & CPS & PH) POST".
    iLöb as "IH".
    rewrite /incr_impl.

    pure_steps.
    
    wp_bind (! _)%E.
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". iModIntro.
    rewrite {1}/cnt_inv_inner. iDestruct "inv" as ">(%c & %wm & CNT & AUTH & WMI & WMEB)".
    iApply sswp_MU_wp; [done| ]. iApply (wp_load with "[$]"). iIntros "!> CNT".
 

  Admitted. 

  
  Lemma incr_spec `{LFCG Σ} τ π cnt π0
    (PH: phase_le π0 π):
    {{{ th_phase_eq τ π ∗ cp_mul π0 d1 2 ∗
        cnt_inv cnt π0 }}}
      incr #cnt @ τ
    {{{ v, RET v; ⌜ True ⌝ }}}.
  Proof using OBLS_AMU INCR_LS_LB DEG01.
    iIntros (Φ) "(PH & CPS1 & #INV) POST".
    rewrite /incr.

    split_cps "CPS1" 1. rewrite -cp_mul_1.
    pure_step_hl. MU_by_BOU.
    iMod (first_BOU with "[$]") as "[CPS #EB]".
    { apply DEG01. }
    rewrite cp_mul_weaken; [| apply PH| reflexivity].
    BOU_burn_cp.

    iApply (incr_impl_spec with "[-POST]").
    { apply PH. }
    { iFrame "#∗". }
    done.
  Qed. 
    
    
