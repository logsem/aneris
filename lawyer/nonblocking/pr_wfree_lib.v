From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From fairness Require Import fairness locales_helpers.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination obligations_wf.
From lawyer.nonblocking Require Import trace_context om_wfree_inst wfree_traces calls.
From trillium.program_logic Require Import execution_model weakestpre adequacy_utils. 
From lawyer Require Import action_model sub_action_em.
From heap_lang Require Import lang.


Close Scope Z.


Lemma pure_and_sep {Σ} (P Q: Prop):
  ((⌜ P ⌝ ∧ ⌜ Q ⌝)%I: iProp Σ) ⊣⊢ (⌜ P ⌝ ∗ ⌜ Q ⌝)%I.
Proof using. clear. simpl. iSplit; set_solver. Qed. 



Section WaitFreePR.

  Let OP := om_hl_OP (OP_HL := OP_HL_WF). 
  Existing Instance OP.
  Let OM := ObligationsModel.

  Let M := AM2M ObligationsAM.
  Let ASEM := ObligationsASEM.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} _ _ => ⌜ True ⌝%I).

  Definition OHE {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}:
    OM_HL_Env OP_HL_WF EM Σ.
  esplit. 
  - apply AMU_lift_top.
  - intros.
    iIntros. iApply AMU_lift_top; [(try rewrite nclose_nroot); done| ].
    iFrame.
    Unshelve.
    exact {| heap_iemgs := Hinv |}.
  Defined.

  Context (ic: @trace_ctx heap_lang).
  Let ii := tctx_index ic.
  Let tc := tctx_tpctx ic. 
  Let Ki := tpctx_ctx tc.
  Let τi := tpctx_tid tc. 

  Definition no_extra_obls (_: cfg heap_lang) (δ: mstate M) :=
    forall τ', default ∅ (ps_obls δ !! τ') ≠ ∅ -> τ' = τi.

  Open Scope WFR_scope. 

  Definition extra_fuel `{!ObligationsGS Σ} F (etr: execution_trace heap_lang) :=
    let len := trace_length etr in
    if len <=? ii then (cp_mul π0 d0 (S ii - len) ∗ cp_mul π0 d0 F)%I else ⌜ True ⌝%I.

  Definition cur_phases `{!ObligationsGS Σ} (etr: execution_trace heap_lang): iProp Σ :=
    let c := trace_last etr in
    ([∗ set] τ ∈ locales_of_cfg c ∖ {[ τi ]}, ∃ π, th_phase_eq τ π) ∗
    let ph_res := let q := if (trace_length etr <=? ii) then 1%Qp else (/2)%Qp in
                  (∃ π, th_phase_frag τi π q)%I in
    ⌜ τi ∈ locales_of_cfg c ⌝ → ph_res.

  Definition obls_τi `{!ObligationsGS Σ}: iProp Σ :=
    ∃ s, obls τi {[ s ]} ∗ sgn s l0 (Some false) ∗ ep s π0 d0. 

  Definition obls_τi' `{!ObligationsGS Σ} (c: cfg heap_lang): iProp Σ :=
    if decide (τi ∈ locales_of_cfg c) then obls_τi else cp π0 d1.

  Definition cur_obls_sigs `{!ObligationsGS Σ} (etr: execution_trace heap_lang): iProp Σ :=
    let c := trace_last etr in
    ([∗ set] τ ∈ locales_of_cfg c ∖ {[ τi ]}, obls τ ∅) ∗
    obls_τi' c. 

  Definition call_progresses s' (etr: execution_trace heap_lang) := 
    s' = NotStuck -> ii < trace_length etr -> 
    not_stuck_tid τi (trace_last etr).

  (* TODO: refactor *)
  Lemma same_phase_no_fork {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    etr mtr
    (e : expr)
    (σ σ' : state)
    (efs t1 t2 : list expr)
    (FIN : trace_last etr = (t1 ++ e :: t2, σ))
    (ec : expr)
    (π : Phase)
    (PH : ps_phases (trace_last mtr) !! τi = Some π)
    (CORR : obls_cfg_corr (trace_last etr) (trace_last mtr))
    (x : expr)
    (H2 : prim_step ec σ x σ' efs)
    (δ' : AM2M ObligationsAM)
    (ℓ : mlabel (AM2M ObligationsAM)):
   ⊢ @th_phase_frag _ _ _ WF_SB OP Σ
           (@iem_fairnessGS heap_lang _ HeapLangEM EM Σ Hinv)
           τi π (/ 2) -∗
  ⌜@obls_ves_wrapper _ _ _ WF_SB
             OP Nat.inhabited (@trace_last (cfg heap_lang) (option nat) etr)
             (@Some nat τi)
             (t1 ++ @fill _ Ki x :: t2 ++ efs, σ')
             (trace_last mtr)
             ℓ δ'⌝ ∗
          @gen_heap_interp loc loc_eq_decision loc_countable (option val) Σ
            (@heap_gen_heapGS Σ (@iem_phys heap_lang _ HeapLangEM EM Σ Hinv))
            (heap σ') ∗
          @obls_asem_mti _ _ _ WF_SB OP
            Nat.inhabited Σ
            (@iem_fairnessGS heap_lang _ HeapLangEM EM Σ Hinv)
            (etr :tr[ @Some nat τi]: (t1 ++ @fill _ Ki x :: t2 ++ efs, σ'))
            (mtr :tr[ ℓ ]: δ') -∗
  ⌜efs = [] /\ locales_of_cfg (trace_last etr) = locales_of_cfg (t1 ++ @fill _ Ki x :: t2 ++ efs, σ')⌝.
  Proof using.
    iIntros "PH HSI".
    iAssert (⌜ ps_phases δ'  !! τi = Some π ⌝)%I as "%PH'".
    { iApply (th_phase_msi_frag with "[-PH] [$]").
      by iDestruct "HSI" as "(?&?&(?&?&?))". }
    iDestruct "HSI" as "(%EVOL&_&CORR')".
    rewrite /obls_asem_mti. simpl. 
    red in EVOL. destruct ℓ as [? [|]].
    2: { tauto. } 
    destruct EVOL as [MSTEP ->]. simpl in MSTEP.
    red in MSTEP. destruct MSTEP as (_ & MSTEP & [=<-] & CORR').
    simpl in MSTEP.
    
    (* TODO: make a lemma *)
    assert (ps_phases (trace_last mtr) = ps_phases δ') as PH_EQ.
    { destruct MSTEP as (δ2 & PSTEP & OFORK).
      destruct PSTEP as (? & ? & δ1 & STEPS & BURN).
      assert (ps_phases (trace_last mtr) = ps_phases δ2) as EQ2. 
      { rewrite (lse_rep_phases_eq_helper _ _ _ STEPS).
        destruct BURN as (?&?&BURN).
        eapply lse_rep_phases_eq_helper.
        apply nsteps_once. red. left.
        eexists. red. eauto. }
      inversion OFORK.
      2: { by subst. }
      subst y. red in H0. destruct H0 as (?&?&FORK).
      inversion FORK. subst.
      subst ps'. rewrite phases_update_phases in PH'.
      subst new_phases0.
      rewrite lookup_insert_ne in PH'.
      2: { intros ->. destruct FRESH'. by eapply elem_of_dom. }
      rewrite lookup_insert in PH'. inversion PH'.
      rewrite -EQ2 PH in LOC_PHASE. inversion LOC_PHASE. subst π0.
      pose proof (phase_lt_fork π 0) as NEQ. red in NEQ.
      apply strict_ne in NEQ. done. }
    
    red in CORR'. destruct CORR' as (CORR' & DPO').

    rewrite (proj1 CORR) (CORR'). 

    red in DPO'. apply (@f_equal _ _ dom) in PH_EQ. 
    rewrite DPO' in PH_EQ.
    red in CORR'. rewrite -PH_EQ in CORR'.
    red in CORR. rewrite (proj2 CORR) -(proj1 CORR) in CORR'.
    rewrite FIN in CORR'. simpl in CORR.
    rewrite !locales_of_cfg_simpl in CORR'.
    repeat (rewrite !length_app /= in CORR').

     iPureIntro. split.
     2: { set_solver. }
    
    destruct efs; [done| ].
    simpl in CORR'. apply set_seq_uniq2 in CORR'. lia.
  Qed.

  Lemma split_trace_fuel {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    F etr c' τ 
    (BEFORE: trace_length etr <= ii):
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    let fuel_pre := cp_mul π0 d0 F in
    ⊢ extra_fuel F etr -∗ cp π0 d0 ∗ fuel_pre ∗
      ((⌜ trace_length etr < ii ⌝ → fuel_pre) -∗ extra_fuel F (etr :tr[ Some τ]: c')).
  Proof using.
    simpl. iIntros "CPS". 
    rewrite /extra_fuel.
    rewrite leb_correct; [| done]. 
    rewrite Nat.sub_succ_l; [| done]. rewrite cp_mul_take.
    iDestruct "CPS" as "((CPS & CP) & CPP)". iFrame.
    iIntros "CPP".
    destruct leb eqn:LEN; [| done]. iFrame.
    iApply "CPP". iPureIntro. 
    apply leb_complete in LEN. simpl in LEN. lia.
  Qed.

  Lemma reestablish_fuel {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    F etr c' τ:
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    ⊢ extra_fuel F etr -∗ extra_fuel F (etr :tr[ Some τ]: c').
  Proof using.
    simpl. iIntros "CPS". 
    rewrite /extra_fuel.
    destruct (trace_length (_ :tr[ _ ]: _) <=? _) eqn:LE; [| done].
    rewrite leb_correct.
    2: { apply leb_complete in LE. simpl in *. lia. }
    simpl. iDestruct "CPS" as "(? & $)".
    iApply (cp_mul_weaken with "[$]"); [done| lia].
  Qed.

  Lemma reestablish_phases {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    etr τ c'
    (EQ_CFG: locales_of_cfg (trace_last etr) = locales_of_cfg c')
    (AFTER: ii < trace_length etr)
    :
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    cur_phases etr -∗ cur_phases (etr :tr[ Some τ ]: c').
  Proof using.
    simpl. iIntros "PHS".
    rewrite /cur_phases.
    rewrite -EQ_CFG.    
    rewrite leb_correct_conv; [| done].
    rewrite leb_correct_conv; [done| ].
    simpl.
    remember (trace_length etr) as X. rewrite -HeqX. lia.
  Qed.

  Lemma reestablish_obls_sigs {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    etr t1 t2 x σ'
    (EQ_CFG: locales_of_cfg (trace_last etr) = locales_of_cfg (t1 ++ fill Ki x :: t2, σ')):
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    cur_obls_sigs etr -∗ cur_obls_sigs (etr :tr[ Some τi ]: (t1 ++ fill Ki x :: t2, σ')).
  Proof using.
    simpl. iIntros "(OBS & OBτi)". 
    rewrite /cur_obls_sigs. simpl.
    rewrite /obls_τi'. 
    rewrite -EQ_CFG. iFrame. 
  Qed.

  From lawyer Require Import program_logic.  

  Lemma MU_burn_cp_nofork {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} τ π d q P:
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    ⊢ BOU ∅ WF_SB (cp π d ∗ th_phase_frag τ π q ∗ P) -∗ 
      let hGS: @heapGS Σ M EM := {| heap_iemgs := Hinv |} in
      @MU _ EM Σ hGS ⊤ τ (th_phase_frag τ π q ∗ P).
  Proof using.
    simpl. iIntros "BOU".
    iApply AMU_lift_top; [(try rewrite nclose_nroot); done| ].
    iApply BOU_AMU. iApply (BOU_weaken with "[] [$]"); try done.
    iIntros "(CP & PH & P)".
    iSplitL "P".
    { by iIntros "$". }
    iFrame.
  Qed.

  Lemma MU_burn_cp_fork {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} τ π0 d τ' Q:
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    ⊢ BOU ∅ WF_SB (∃ R1 R2, cp π0 d ∗ th_phase_eq τ π0 ∗ obls τ (R1 ∪ R2) ∗ Q R1 R2 ∗ ⌜ R1 ## R2 ⌝) -∗
      let hGS: @heapGS Σ M EM := {| heap_iemgs := Hinv |} in
      @MU__f _ EM Σ hGS ⊤ τ τ'
        (∃ π π' R1 R2, th_phase_eq τ π ∗ th_phase_eq τ' π' ∗ obls τ R1 ∗ obls τ' R2 ∗ Q R1 R2 ∗ ⌜ R1 ## R2 ⌝).
  Proof using.
    simpl. iIntros "BOU".
    iApply AMU_lift_top; [(try rewrite nclose_nroot); done| ].
    iApply (BOU_AMU__f'_strong _ _ _ _ Q). iApply (BOU_weaken with "[] [$]"); try done. 
    iIntros "(%R1 & %R2 & CP & PH & OB & Q &?)".
    iFrame. 
    iIntros "(%&%&%&%&?&?&?&?&?&?)".
    iFrame. 
  Qed.

  Lemma MU_burn_cp {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} τ π0 d oτ' Q:
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    ⊢ BOU ∅ WF_SB (∃ R1 R2, cp π0 d ∗ th_phase_eq τ π0 ∗ obls τ (R1 ∪ R2) ∗ Q R1 R2 ∗ ⌜ R1 ## R2 ⌝) -∗
      let hGS: @heapGS Σ M EM := {| heap_iemgs := Hinv |} in
      @MU_impl _ EM Σ hGS oτ' ⊤ τ
        (∃ π R1 R2, th_phase_eq τ π ∗ Q R1 R2 ∗ ⌜ R1 ## R2 ⌝ ∗
         from_option (fun τ' => ∃ π', th_phase_eq τ' π' ∗ obls τ R1 ∗ obls τ' R2) (obls τ (R1 ∪ R2)) oτ').
  Proof using.
    simpl. iIntros "BOU".
    destruct oτ'.
    - iPoseProof (MU_burn_cp_fork with "[$]") as "foo".
      iApply (MU__f_wand with "[] [$]"). simpl.
      iIntros "(%&%&%&%&?&?&?&?&?)". by iFrame.
    - simpl.
      iApply (MU_wand with "[-BOU]").
      2: { iApply MU_burn_cp_nofork. iMod "BOU".
           repeat setoid_rewrite <- bi.sep_exist_l. 
           iModIntro. iFrame. }
      iIntros "[$ X]". by iDestruct "X" as "(%&%&$&?)". 
  Qed.

  Lemma cur_obls_sigs_τi_step `{!ObligationsGS Σ} etr c'
    (STEP: locale_step (trace_last etr) (Some τi) c'):
    cur_obls_sigs etr -∗ obls_τi ∗
      let oτ' := step_fork (trace_last etr) c' in
      (obls_τi -∗ from_option (fun τ' => obls τ' ∅) ⌜ True ⌝ oτ' -∗ cur_obls_sigs (etr :tr[ Some τi ]: c')).
  Proof using.
    simpl. iIntros "(OBLS & OB)".
    rewrite /cur_obls_sigs /obls_τi'. simpl.
    rewrite decide_True.
    2: { eapply locales_of_cfg_step; eauto. }
    iFrame. iIntros "OB OB'". 
    rewrite decide_True.
    2: { eapply locale_step_sub; eauto. eapply locales_of_cfg_step; eauto. }
    iFrame.
    pose proof STEP as ->%locale_step_step_fork_exact. 
    rewrite difference_union_distr_l_L big_sepS_union.
    2: { destruct step_fork eqn:SF; [| set_solver].
         simpl. apply elem_of_disjoint.
         intros ? [??]%elem_of_difference [->%elem_of_singleton ?]%elem_of_difference.
         apply step_fork_difference in SF. set_solver. }
    iFrame. destruct step_fork eqn:SF; simpl. 
    2: { rewrite subseteq_empty_difference_L; set_solver. }
    rewrite difference_disjoint_L.
    2: { apply step_fork_difference in SF.
         apply locales_of_cfg_step in STEP.
         set_solver. }
    by rewrite big_sepS_singleton.
  Qed.

  Lemma cur_phases_τi_step `{!ObligationsGS Σ} etr c'
    (STEP: locale_step (trace_last etr) (Some τi) c'):
    cur_phases etr -∗
    let oτ' := step_fork (trace_last etr) c' in
    let ph ex := ∃ π, th_phase_frag τi π (if (trace_length ex <=? ii) then 1%Qp else (/2)%Qp) in
    let etr' := etr :tr[ Some τi ]: c' in
    ph etr ∗ (ph etr' -∗ from_option (fun τ' => ∃ π', th_phase_eq τ' π') ⌜ True ⌝ oτ' -∗ cur_phases etr').
  Proof using.
    #[local] Arguments Nat.leb _ _ : simpl nomatch.
    rewrite /cur_phases. simpl. iIntros "(PHS & PH)".
    iSpecialize ("PH" with "[]").
    { iPureIntro. eapply locales_of_cfg_step; eauto. }
    iFrame.
    iIntros "PH PH'".
    pose proof STEP as ->%locale_step_step_fork_exact. 
    rewrite difference_union_distr_l_L big_sepS_union.
    2: { destruct step_fork eqn:SF; [| set_solver].
         simpl. apply elem_of_disjoint.
         intros ? [??]%elem_of_difference [->%elem_of_singleton ?]%elem_of_difference.
         apply step_fork_difference in SF. set_solver. }
    iFrame "PHS".

    iSplitL "PH'".
    { destruct step_fork eqn:SF.
      2: { simpl. rewrite subseteq_empty_difference_L; set_solver. }
      simpl. rewrite difference_disjoint_L.
      { by rewrite big_sepS_singleton. }
      apply elem_of_disjoint. intros ? ?%elem_of_singleton ?%elem_of_singleton. 
      subst.
      apply step_fork_difference in SF.
      apply locales_of_cfg_step in STEP. set_solver. }
    iFrame. done. 
  Qed.

  Lemma cur_obls_sigs_other_step `{!ObligationsGS Σ}
    etr c' τ
    (STEP: locale_step (trace_last etr) (Some τ) c')
    (OTHER: τ ≠ τi)
    :
    cur_obls_sigs etr -∗
      obls τ ∅ ∗ obls_τi' (trace_last etr) ∗
      let oτ' := step_fork (trace_last etr) c' in
      (obls τ ∅ -∗ obls_τi' c' -∗ (∀ τ', ⌜ oτ' = Some τ' /\ τ' ≠ τi ⌝ → obls τ' ∅) -∗
       cur_obls_sigs (etr :tr[ Some τi ]: c')).
  Proof using.
    simpl. iIntros "(OBLS & OBτi)". iFrame "OBτi". 
    rewrite /cur_obls_sigs. simpl.
    iDestruct (big_sepS_elem_of_acc with "[$]") as "(OB & OBLS)".
    { apply elem_of_difference. split; [| apply not_elem_of_singleton]; eauto.
      eapply locales_of_cfg_step; eauto. }
    iFrame "OB". iIntros "OB OBτi OB'".
    iSpecialize ("OBLS" with "[$]").     
    pose proof STEP as ->%locale_step_step_fork_exact.    
    rewrite difference_union_distr_l_L big_sepS_union.
    2: { destruct step_fork eqn:SF; [| set_solver].
         simpl. apply elem_of_disjoint.
         intros ? [??]%elem_of_difference [->%elem_of_singleton ?]%elem_of_difference.
         apply step_fork_difference in SF. set_solver. }
    iFrame.
    destruct step_fork eqn:SF; simpl. 
    2: { rewrite subseteq_empty_difference_L; set_solver. }
    destruct (decide (l = τi)).
    { rewrite subseteq_empty_difference_L; set_solver. } 
    rewrite difference_disjoint_L; [| set_solver].
    rewrite big_sepS_singleton. by iApply "OB'". 
  Qed.

  (* TODO: refactor *)
  Lemma cur_phases_other_step `{!ObligationsGS Σ} etr c' τ
                              m ai
    (STEP: locale_step (trace_last etr) (Some τ) c')
    (* (etr' := etr :tr[ Some τi ]: c') *)
    (etr' := etr :tr[ Some τ ]: c')
    (FITS: fits_inf_call ic m ai etr')
    (OTHER: τ ≠ τi):
    cur_phases etr -∗
    let oτ' := step_fork (trace_last etr) c' in
    let ph := ∃ π, th_phase_eq τ π in
    ph ∗ (ph -∗ from_option (fun τ' => ∃ π', th_phase_eq τ' π') ⌜ True ⌝ oτ' -∗
          cur_phases etr' ∗
          (⌜ trace_length etr = ii ⌝ → ∃ π, th_phase_frag τi π (/2)%Qp)).
  Proof using.
    rewrite /cur_phases. simpl. iIntros "(PHS & PHτi)".
    iDestruct (big_sepS_elem_of_acc with "[$]") as "(PH & PHS)".
    { apply elem_of_difference. split; [| apply not_elem_of_singleton]; eauto.
      eapply locales_of_cfg_step; eauto. }
    iFrame "PH". iIntros "PH PH'".
    iSpecialize ("PHS" with "[$]"). 
    pose proof STEP as ->%locale_step_step_fork_exact. 
    rewrite difference_union_distr_l_L big_sepS_union.
    2: { destruct step_fork eqn:SF; [| set_solver].
         simpl. apply elem_of_disjoint.
         intros ? [??]%elem_of_difference [->%elem_of_singleton ?]%elem_of_difference.
         apply step_fork_difference in SF. set_solver. }
    iFrame "PHS". rewrite -bi.sep_assoc. 
    
    destruct step_fork eqn:SF.
    2: { simpl. iSplitR.
         { rewrite subseteq_empty_difference_L; [| done]. set_solver. }
         rewrite union_empty_r_L. 
         destruct (decide (trace_length etr = ii)).
         - destruct FITS. 
           rewrite trace_lookup_last in fic_call .
           2: { simpl in *. lia. }
           simpl in fic_call. 
           iSpecialize ("PHτi" with "[]").
           { iPureIntro. red in fic_call. 
             pose proof STEP as EQ%locale_step_step_fork_exact.
             rewrite SF /= union_empty_r_L in EQ. rewrite -EQ.
             eapply expr_at_in_locales; eauto. }
           iDestruct "PHτi" as (?) "PH".
           rewrite leb_correct; [| simpl in *; lia].
           iDestruct (th_phase_frag_halve with "PH") as "[PH PH_]".
           rewrite leb_correct_conv; [| simpl in *; lia].
           rewrite half_inv2. iSplitL "PH".
           + iIntros "_". iFrame.
           + iIntros "_". iFrame.
         - iSplitL.
           2: { by iIntros (?). }
           simpl. 
           assert (S (trace_length etr) <=? ii = (trace_length etr <=? ii)) as X. 
           2: { rewrite X. iFrame. }
           simpl in *.
           destruct (decide (trace_length etr <= ii)) as [LE | GT]. 
           + by do 2 (rewrite leb_correct; [| lia]).
           + by do 2 (rewrite leb_correct_conv; [| lia]). }

    simpl. 
    destruct (decide (l = τi)) as [-> | ?]. 
    { rewrite subseteq_empty_difference_L; [| set_solver]. iSplitR; [set_solver| ].
      iDestruct "PH'" as (?) "PH".
      destruct (decide (trace_length etr = ii)).
      - rewrite leb_correct; [| simpl in *; lia].
        iDestruct (th_phase_frag_halve with "PH") as "[PH PH_]".
        rewrite leb_correct_conv; [| simpl in *; lia].
        rewrite half_inv2. iSplitL "PH".
        + iIntros "_". iFrame.
        + iIntros "_". iFrame.
      - iSplitL.
        2: { by iIntros (?). }
        simpl.
        iClear "PHτi". iIntros "_".
        rewrite leb_correct; [iFrame| ].
        enough ((trace_length etr) ≤ ii).
        { simpl in *. lia. }
        destruct (Nat.le_gt_cases (trace_length etr) ii); [done| ].
        eapply fic_has_τi in H. 
        2: { eapply fits_inf_call_prev; eauto. }
        apply step_fork_difference in SF. set_solver. }

    simpl. rewrite difference_disjoint_L.
    2: { set_solver. }
    rewrite big_opS_singleton. iFrame "PH'".

    destruct (decide (trace_length etr = ii)).
    - destruct FITS. subst etr'.
      rewrite trace_lookup_last in fic_call.
      2: { simpl in *. lia. }
      simpl in fic_call.
      iSpecialize ("PHτi" with "[]").
      { iPureIntro. red in fic_call. 
        pose proof STEP as EQ%locale_step_step_fork_exact.
        rewrite SF /= in EQ.
        apply expr_at_in_locales in fic_call. rewrite EQ in fic_call.
        apply elem_of_union in fic_call as [|]; eauto.
        set_solver. }
      iDestruct "PHτi" as (?) "PH".
      rewrite leb_correct; [| simpl in *; lia].
      iDestruct (th_phase_frag_halve with "PH") as "[PH PH_]".
      rewrite leb_correct_conv; [| simpl in *; lia].
      rewrite half_inv2. iSplitL "PH".
      + iIntros "_". iFrame.
      + iIntros "_". iFrame.
    - iSplitL. 
      2: { by iIntros (?). }
      simpl. 
      assert (S (trace_length etr) <=? ii = (trace_length etr <=? ii)) as X. 
      2: { rewrite X.
           iIntros (?). iApply "PHτi".
           iPureIntro. set_solver. }
      simpl in *.
      destruct (decide (trace_length etr <= ii)) as [LE | GT]. 
      + by do 2 (rewrite leb_correct; [| lia]).
      + by do 2 (rewrite leb_correct_conv; [| lia]).
  Qed.

  Lemma obls_τi'_next `{!ObligationsGS Σ} c c'
    (SAME: locales_of_cfg c' = locales_of_cfg c):
    obls_τi' c ⊣⊢ obls_τi' c'.
  Proof using.
    rewrite /obls_τi'. by rewrite SAME.
  Qed.

  Lemma BOU_wait_τi `{!ObligationsGS Σ} `{invGS_gen HasNoLc Σ} τ π:
    obls τ ∅ -∗ th_phase_eq τ π -∗ obls_τi -∗
      BOU ∅ WF_SB (cp π d0 ∗ th_phase_eq τ π ∗ obls τ ∅ ∗ obls_τi). 
  Proof using.
    iIntros "OB PH OBτi".
    rewrite /obls_τi. iDestruct "OBτi" as "(%s & OBτi & SGN & #EP)".    
    iMod (expect_sig_upd with "[] [$] OB [] [$]") as "(?&?&?&?)".
    { iApply (ep_weaken with "[$]"). apply (phase_le_init π). } 
    { (* TODO: Make a lemma *)
      rewrite /sgns_level_gt. rewrite /sgns_levels_gt'.
      iApply empty_sgns_levels_rel. }
    { rewrite /WF_SB. lia. }
    iModIntro. iFrame "#∗".
  Qed.

  Lemma locale_tp_split
          c'
    (e e' : expr) (σ' : state) (efs t1 t2 : list expr)
    (Heqc': (t1 ++ e' :: t2 ++ efs, σ') = c')
    (τ := locale_of t1 e):
    (locale_of t1 e ∉ locales_of_list t1) ∧
    (locale_of t1 e ∉ locales_of_list_from (t1 ++ [e']) t2) ∧
    locale_of t1 e ∉ locales_of_list_from (t1 ++ [e'] ++ t2) efs.
  Proof using.
    pose proof (thread_pool_split c'.1 τ) as SPLIT.
    rewrite -Heqc' /= in SPLIT. destruct SPLIT as (tp1 & tp2 & tp' & EQ & TP' & NO1 & NO2).
    destruct TP' as [-> | (e_ & -> & LOC)].
    { simpl in EQ.
      assert (τ ∈ locales_of_list c'.1) as IN. 
      { rewrite -Heqc' /=.
        rewrite locales_of_list_from_app /=. rewrite locales_of_list_from_cons.
        set_solver. }
      rewrite -Heqc' /= EQ in IN.
      rewrite locales_of_list_from_app /= in IN.
      rewrite app_nil_r in NO2.
      exfalso. 
      apply elem_of_app in IN as [?|?]; eauto. }
    rewrite -/τ /locale_of in LOC.
    apply app_inj_1 in EQ as [EQ1 EQ2]; eauto.
    simpl in EQ2. inversion EQ2. subst.
    split; eauto.
    apply Decidable.not_or. intros IN. destruct NO2.
    rewrite locales_of_list_from_app. apply elem_of_app.
    by rewrite -app_assoc.
  Qed.

  Lemma τi_not_in
          (etr: execution_trace heap_lang) ee
    e σ e' σ'
  (efs t1 t2 : list expr)
  (FIN' : trace_last etr = (t1 ++ e :: t2, σ))
  (τ := locale_of t1 e : nat)
  (STEP : locale_step (t1 ++ e :: t2, σ) (Some τ) (t1 ++ e' :: t2 ++ efs, σ'))
  (NO : step_fork (trace_last etr) (t1 ++ e' :: t2 ++ efs, σ') ≠ Some τi)
  (FIT : from_locale (t1 ++ e' :: t2 ++ efs) τi = Some ee)
  (sf := step_fork (trace_last etr) (t1 ++ e' :: t2 ++ efs, σ')):
  τi ∉ locales_of_list_from (t1 ++ e' :: t2) efs.
  Proof using.
    rewrite locales_of_list_from_locales.
    intros [[??] IN]%elem_of_list_In%in_map_iff.
    destruct IN as (LOC & IN).
    apply elem_of_list_In, elem_of_list_lookup in IN as [i IN].
    pose proof IN as X.
    apply prefixes_from_ith_length in IN. 
    rewrite !length_app /= in IN. rewrite /locale_of in LOC.
    
    apply from_locale_lookup in FIT.
    apply lookup_lt_Some in FIT. simpl in FIT.
    rewrite /τi in LOC.
    rewrite /τi -LOC IN in FIT. 
    repeat rewrite !length_app /= in FIT.
    simpl in FIT.
    
    apply step_fork_hl in STEP as [[? ->] | (?&->&?)].
    { simpl. simpl in FIT. lia. }
    simpl in FIT. destruct i; [| lia].
    simpl in X. inversion X.
    subst. simpl in e0.
    rewrite app_comm_cons app_assoc in NO.
    rewrite FIN' in NO.
    rewrite step_fork_fork in NO.
    { rewrite /τi in NO. 
      rewrite -LOC in NO. 
      rewrite /locale_of !length_app in NO. done. }
    apply locales_equiv_middle. done.
  Qed.

  (* TODO: this doesn't rely on (oτ ≠ Some τi)? can it be reused?*)
  Lemma take_model_step {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    c (etr: execution_trace heap_lang)
    t1 e' t2 efs σ' π e
    (oτ' := step_fork c (t1 ++ ectx_fill ectx_emp e' :: t2 ++ efs, σ'))
    (τ := locale_of t1 e)
    (FIN': trace_ends_in etr c)
    (STEP: locale_step c (Some τ) (t1 ++ ectx_fill ectx_emp e' :: t2 ++ efs, σ'))
:
    let oGS: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    cp π0 d0 -∗ th_phase_eq τ π -∗ obls (locale_of t1 e) ∅ -∗ obls_τi' (trace_last etr) -∗     
    @MU_impl _
          EM Σ {| heap_iemgs := Hinv |} oτ' ⊤
          τ
          (∃ (π0 : Phase) (R1 R2 : @gset SignalId Nat.eq_dec nat_countable),
             th_phase_eq τ π0 ∗
             (λ R0 R3 : gset SignalId,
                let H :=
                  @iem_fairnessGS heap_lang
                    (AM2M
                       (@ObligationsAM Degree Level (locale heap_lang) WF_SB OP
                          Nat.inhabited))
                    HeapLangEM EM Σ Hinv
                  in
                ⌜R0 = ∅⌝ ∗
                (if
                  decide (oτ' = @Some (locale heap_lang) τi)                    
                 then
                  ∃ s0, ⌜R3 = {[s0]}⌝ ∗
                    sgn s0 l0 (Some false) ∗
                    ep s0 obligations_model.π0 d0
                 else ⌜R3 = ∅⌝ ∗ @obls_τi' Σ H (t1 ++ e' :: t2 ++ efs, σ')))
               R1 R2 ∗
             ⌜R1 ## R2⌝ ∗
             @from_option (locale heap_lang) (iPropI Σ)
               (λ τ' : locale heap_lang,
                  ∃ π' : Phase,
                    th_phase_eq τ' π' ∗
                    obls τ R1 ∗
                    obls τ' R2)
               (obls τ (R1 ∪ R2)) oτ').
  Proof using.
    simpl. iIntros "CP PH OB OBτi".
    rewrite (cp_weaken _ π); [| by apply phase_le_init].
    rewrite /obls_τi' /obls_τi.
    
    iApply (MU_burn_cp with "[-]").
    iFrame "CP PH". simpl.
    rewrite -FIN' in STEP.

    assert (exists sf, sf = oτ') as (sf & Heqsf) by eauto. subst oτ'.
    rewrite FIN' in STEP.
    rewrite -Heqsf. 

    destruct sf; simpl.
    2: { iModIntro. do 2 iExists _.
         iSplitL "OB".
         { erewrite union_empty_r_L. iFrame. }
         repeat (iSplit; try done).
         iApply obls_τi'_next; [| done].
         apply locale_step_step_fork_exact in STEP.
         rewrite -Heqsf /= in STEP.
         rewrite STEP. rewrite FIN'. set_solver. }
    destruct (decide (l = τi)) as [-> | NEQ].
    - rewrite decide_False.
      2: { eapply locale_step_fork_Some in STEP; eauto.
           rewrite FIN'. tauto. }
      iMod (OU_create_sig with "[$]") as "(%sg & SGN & OB & _)".
      { rewrite /WF_SB. lia. }
      iDestruct (sgn_get_ex with "[$]") as "(SGN & #SGN0)".
      iMod (create_ep_upd with "[OBτi] SGN0") as "(#EP & _)".
      { apply (orders_lib.ith_bn_lt 2 0 1). lia. }
      { iFrame. }
      iModIntro. do 2 iExists _. rewrite decide_True; [| done].
      iFrame. iFrame "#∗". iPureIntro. set_solver.
    - iModIntro. iFrame.
      setoid_rewrite (@decide_False _ (Some l = _)); [| congruence].
      do 2 iExists _. erewrite union_empty_r_L. iFrame.
      repeat iSplit; try done.
      rewrite /obls_τi'.
      apply locale_step_step_fork_exact in STEP. rewrite STEP.
      erewrite decide_ext; [by iFrame| ].
      rewrite -Heqsf. simpl.
      rewrite FIN'. set_solver.
  Qed.

End WaitFreePR.
