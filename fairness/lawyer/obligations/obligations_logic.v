From iris.proofmode Require Import tactics coq_tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From trillium.fairness Require Import locales_helpers utils. 
From trillium.fairness.lawyer.obligations Require Import obligations_model obls_utils obligations_resources obligations_am obligations_em obligations_wf.
From trillium.fairness.lawyer Require Import sub_action_em program_logic action_model.
From trillium.fairness.heap_lang Require Export heap_lang_defs tactics notation sswp_logic locales_helpers_hl.


Close Scope Z.

(* some lemmas about heap lang rely on concrete instances of EqDecision and Countable *)
(* TODO: find better solution *)
Class ObligationsParamsPre (Degree Level: Type) (LIM_STEPS: nat) := { 
    opar_deg_eqdec' :> EqDecision Degree;
    opar_deg_cnt' :> Countable Degree;
    deg_le' :> relation Degree;
    deg_PO' :> PartialOrder deg_le';

    opar_lvl_eqdec':> EqDecision Level;
    opar_lvl_cnt':> Countable Level;
    lvl_le':> relation Level;
    lvl_PO':> PartialOrder lvl_le';
  }.

Global Instance LocaleOP
  `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}
  `{CNT: Countable Locale}:
  ObligationsParams Degree Level Locale LIM_STEPS.
Proof using.
  esplit; try by apply OPRE. apply CNT.
Defined.                 


Section ProgramLogic.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.
  
  (* Context `{OP: ObligationsParams Degree Level (locale heap_lang) LIM_STEPS}. *)
  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP. 
  Let OM := ObligationsModel.
  
  Context {Σ: gFunctors}.
  Context {invs_inΣ: invGS_gen HasNoLc Σ}.

  Let OAM := ObligationsAM. 
  Let ASEM := ObligationsASEM.

  Goal @asem_GS _ _ ASEM Σ = ObligationsGS (OP := OP) Σ.
    reflexivity.
  Abort. 

  (* Keeping the more general interface for future developments *)
  Context {oGS': @asem_GS _ _ ASEM Σ}.
  Let oGS: ObligationsGS (OP := OP) Σ := oGS'.
  Existing Instance oGS. 
  
  Section BOU.

    (* TODO: move to _em ? *)
    Lemma occ_pres_by_progress δ1 τ δ2 c
      (OCC: obls_cfg_corr c δ1)
      (PSTEP: progress_step δ1 τ δ2):
      obls_cfg_corr c δ2.
    Proof using.
      split. 
      - red. apply proj1 in OCC.
        rewrite OCC.
        unshelve eapply (pres_by_loc_step_implies_progress _ _ _ _ _) in PSTEP.
        { apply loc_step_dom_obls_pres. }
        2: reflexivity.
        symmetry. apply PSTEP.
      - unshelve eapply (pres_by_loc_step_implies_progress _ _ _ _ _) in PSTEP.
        { apply loc_step_dpo_pres. }
        { done. }
        by apply OCC.
    Qed.

    Lemma BOU_AMU E ζ π q P:
      ⊢ BOU E LIM_STEPS ((th_phase_frag ζ π q -∗ P) ∗ ∃ d, cp π d ∗ th_phase_frag ζ π q) -∗
         AMU E ζ obls_act P (aeGS := oGS').
    Proof using.
      rewrite /AMU /AMU_impl. iIntros "BOU" (c c' δ) "TI'".
      rewrite /AM_st_interp_interim. iDestruct "TI'" as "(MSI&%STEP&%FORK)".

      simpl. rewrite /obls_si. iDestruct "MSI" as "[MSI %CORR]".
      iMod (obls_msi_interim_progress with "[$] [BOU]") as "X".
      { iApply (BOU_wand with "[-BOU] [$]"). iFrame.
        rewrite bi.sep_comm. rewrite bi.sep_exist_r.
        setoid_rewrite bi.sep_assoc.
        iIntros "X". iApply "X". }
      iDestruct "X" as (δ') "(MSI & %PSTEP & PH & P)".
      iSpecialize ("P" with "[$]"). 
      iModIntro. iExists δ', (Some ζ). iFrame. 
      iPureIntro. simpl.

      assert (obls_cfg_corr c' δ') as OCC'.
      { eapply occ_pres_by_progress in PSTEP; [| eauto].
        destruct PSTEP as [TOO DPO]. split; auto.
        red. rewrite -TOO.
        apply gset_pick_None in FORK. 
        apply set_eq_subseteq. split. 
        - apply empty_difference_subseteq_L in FORK. set_solver.
        - eapply locale_step_sub; eauto. }
        
      split; auto. split; [| auto].
      red. repeat split; try by apply OCC' || done.
      simpl. eexists. split; eauto. by right.
    Qed.

    (* TODO: move *)
    Lemma locale_step_fork_Some c1 τ c2 τ'
      (STEP: locale_step c1 (Some τ) c2)
      (FORK: step_fork c1 c2 = Some τ'):
      locales_of_cfg c2 = locales_of_cfg c1 ∪ {[τ']} ∧ τ' ∉ locales_of_cfg c1.
    Proof using.
      apply gset_pick_Some in FORK.
      eapply locale_step_fresh_exact in FORK; eauto.
    Qed.

    Lemma BOU_AMU__f E ζ ζ' π R0 R' P:
      ⊢
        (* (th_phase_eq ζ π -∗ BOU E b *)
        (*    (P ∗ (∃ ph deg, cp ph deg ∗ ⌜ phase_le ph π ⌝) ∗ *)
        (*    th_phase_eq ζ π ∗ *)
        (*    obls ζ R0) (oGS := oGS)) -∗ *)
        (* th_phase_eq ζ π -∗ *)
        (* AMU__f E ζ ζ' obls_act (P ∗ ∃ π1 π2,  *)
        (*              th_phase_eq ζ π1 ∗ obls ζ (R0 ∖ R') ∗ *)
        (*              th_phase_eq ζ' π2 ∗ obls ζ' (R0 ∩ R') ∗ *)
        (*              ⌜ phase_lt π π1 /\ phase_lt π π2 ⌝ *)
        (* ) (aeGS := oGS'). *)

        BOU E LIM_STEPS (P ∗ ∃ d, cp π d ∗ obls ζ R0 ∗ th_phase_eq ζ π) -∗
        AMU__f E ζ ζ' obls_act (P ∗ ∃ π1 π2,
            th_phase_eq ζ π1 ∗ obls ζ (R0 ∖ R') ∗ 
            th_phase_eq ζ' π2 ∗ obls ζ' (R0 ∩ R') ∗
            ⌜ phase_lt π π1 /\ phase_lt π π2 ⌝) (aeGS := oGS').
    Proof using.
      clear H1 H0 H. 
      rewrite /AMU__f /AMU_impl. iIntros "BOU" (c c' δ) "TI'".
      iDestruct "TI'" as "(MSI&%STEP&%FORK)". iFrame. 
      iDestruct "MSI" as "(MSI&%OBLS&%DPO)".
      iMod (obls_msi_interim_omtrans_fork with "[$] [BOU]") as "X".
      3: { iApply (BOU_wand with "[-BOU] [$]"); try done.
           rewrite bi.sep_comm bi.sep_exist_r.
           repeat setoid_rewrite bi.sep_assoc. iIntros "X". iApply "X". }
      { eapply locale_step_fork_Some in FORK; eauto.
        apply proj2 in FORK. rewrite OBLS -DPO in FORK. eauto. }
      { eauto. }
      iDestruct "X" as (δ'' π1 π2) "(SI & OB1 & PH1 & OB2 & PH3 & ((%PH1 & %PH2) & %TRANS & P))".
      iFrame "P".
      iModIntro. repeat setoid_rewrite bi.sep_exist_l.
      iDestruct (th_phase_msi_frag with "[$] PH3") as %PH_NEW.
      iExists _, (Some ζ). do 2 iExists _. iFrame. iPureIntro.
      apply and_assoc. split; [| done].

      destruct TRANS as (δ' & PSTEP & MFORK).
      pose proof PSTEP as OCC'. 
      eapply occ_pres_by_progress in OCC'.
      2: { split; eauto. }
      assert (obls_cfg_corr c' δ'') as OCC''.
      { red. split.
        2: { eapply fork_step_dpo_pres; [| eauto]. apply OCC'. }
        red. destruct OCC' as [TOO' DPO'].
        eapply locale_step_fork_Some in FORK; eauto. rewrite (proj1 FORK).
        rewrite TOO'.
        red in MFORK. destruct MFORK as (?&?& X). inversion X. subst. 
        subst ps'. destruct δ'. subst new_obls0. simpl in *.
        assert (x = ζ') as ->.
        2: { enough (ζ ∈ dom ps_obls).
             { clear -H. set_solver. }
             rewrite -DPO'. simpl. eapply elem_of_dom; eauto. }
        move PH_NEW at bottom. subst new_phases0.
        destruct (decide (x = ζ')); [done| ].
        rewrite lookup_insert_ne in PH_NEW; [| done].
        rewrite lookup_insert_ne in PH_NEW.
        2: { intros <-. apply (proj2 FORK).
             rewrite TOO' -DPO'. simpl.
             eapply elem_of_dom; eauto. }
        destruct (proj2 FORK).
        rewrite TOO' -DPO'. simpl.
        eapply elem_of_dom; eauto. }
      
      split; [done| ]. simpl. split; auto.
      red. do 2 (split; auto). 
      eexists. split; eauto. by left.  
    Qed.

  End BOU.

End ProgramLogic.


Section TestProg.
  
  Let test_prog: expr :=
        let: "x" := ref (#1 + #1) in
        Fork(!"x")
  .

  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.
  
  (* Context `{OP: ObligationsParams Degree Level (locale heap_lang) LIM_STEPS}. *)
  (* Let OM := ObligationsModel. *)
  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP. 
  Let OM := ObligationsModel.

  Let OAM := ObligationsAM. 
  Let ASEM := ObligationsASEM.
  (* Keeping the more general interface for future developments *)
  Context `{oGS': @asem_GS _ _ ASEM Σ}.
  Let oGS: ObligationsGS (OP := OP) Σ := oGS'.
  Existing Instance oGS.

  Hypothesis (LIM_STEPS_LB: 5 <= LIM_STEPS).

  Context `{EM: ExecutionModel heap_lang M}. 
  Context `{hGS: @heapGS Σ _ EM}.

  Context {OBLS_AMU: @AMU_lift_MU _ _ _ oGS' _ EM _ (↑ nroot)}.
  Context {OBLS_AMU__f: forall τ, @AMU_lift_MU__f _ _ _ τ oGS' _ EM _ (↑ nroot)}.
 
  Context {NO_OBLS_POST: ⊢ ∀ τ, obls τ ∅ -∗ 
                                  em_thread_post τ (em_GS0 := heap_fairnessGS (heapGS := hGS))}.
  
  Lemma test_spec (τ: locale heap_lang) (π: Phase) (d d': Degree) (l: Level)
    (DEG: deg_lt d' d)
    :
    {{{ cp_mul π d 10 ∗ th_phase_eq τ π ∗ obls τ ∅ ∗ exc_lb 5 }}}
      test_prog @ τ
      {{{ x, RET #x; obls τ ∅ }}}.
  Proof.
    iIntros (Φ). iIntros "(CPS & PH & OBLS & #EB) POST".
    rewrite /test_prog. 

    wp_bind (_ + _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step; [done| ].
    rewrite /Z.add. simpl. 
    iNext.

    iApply OBLS_AMU; [by rewrite nclose_nroot| ].
    iApply (BOU_AMU with "[-]").
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
    iMod (exchange_cp_upd with "[$] [$]") as "CPS'"; eauto; [lia| ].
    iModIntro. 
    iDestruct (cp_mul_take with "CPS'") as "[CPS' CP']". 
    iSplitR "CP' PH".
    2: { iExists _. iFrame. }
    iIntros "PH".

    iApply wp_value.

    wp_bind (ref _)%E. 
    iApply sswp_MU_wp; [done| ].
    iApply wp_alloc. iIntros "!> %x L ?".
    iApply OBLS_AMU; [by rewrite nclose_nroot| ].
    iApply BOU_AMU. 
    iMod (OU_create_sig _ _ l with "[$]") as "SIG"; [lia| ].
    iDestruct "SIG" as "(%sid & SIG & OBLS & %NEW)".
    iModIntro.
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
    iSplitR "CP PH". 
    2: { iExists _. iFrame. }
    iIntros "PH".

    iApply wp_value.

    wp_bind (Rec _ _ _). 
    iApply sswp_MU_wp; [done| ].      
    iApply sswp_pure_step; [done| ].
    iNext. iApply OBLS_AMU; [by rewrite nclose_nroot| ].
    iApply BOU_AMU. 
    iModIntro.
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
    iSplitR "CP PH".
    2: { iExists _. iFrame. }
    iIntros "PH".
    rewrite union_empty_l_L. 

    iApply wp_value. 

    iApply sswp_MU_wp; [done| ].      
    iApply sswp_pure_step; [done| ].
    iNext. iApply OBLS_AMU; [by rewrite nclose_nroot| ].
    iApply BOU_AMU. iModIntro. 
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
    iSplitR "CP PH". 
    2: { iExists _. iFrame. }
    iIntros "PH".

    simpl.

    iApply sswp_MUf_wp. iIntros (τ'). iApply (MU__f_wand with "[]").
    2: {
      iApply OBLS_AMU__f; [by rewrite nclose_nroot| ]. 
      iApply BOU_AMU__f.
      iNext. 
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
      iMod (burn_cp_upd with "CP [$]") as "PH"; [lia| ].
      iModIntro. iFrame "PH OBLS".
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
      iSplitR "CP".
      2: { iExists _. iFrame. }
      iAccu.
    }

    iIntros "[(POST & CPS' & L & MT & SIG & CPS) R']".
    iDestruct "R'" as (π1 π2) "(PH1 & OB1 & PH3 & OB2 & [%LT1 %LT2])".

    iSplitR "POST CPS MT OB1 PH1"; cycle 1.  
    - iApply "POST". 
      iApply (obls_proper with "[$]").
      symmetry. apply subseteq_empty_difference. reflexivity.
    - iApply sswp_MU_wp; [done| ].
      iApply (wp_load with "[$]"). iNext. iIntros.
      iApply OBLS_AMU; [by rewrite nclose_nroot| ].
      iApply BOU_AMU.
      iMod (OU_set_sig with "OB2 SIG") as "SIG"; [set_solver| lia| ].
      iDestruct "SIG" as "[SIG OB2]".
      iModIntro. 
      iDestruct (cp_mul_take with "CPS'") as "[CPS' CP]".
      iSplitR "CP PH3".
      2: { iExists _. iFrame "PH3".
           iApply (cp_weaken with "[$]"). apply LT2. }

      iIntros "PH". 
      iApply wp_value.
      simpl.
      iApply NO_OBLS_POST. 
      iApply (obls_proper with "[$]").
      set_solver.
  Qed.

End TestProg.
