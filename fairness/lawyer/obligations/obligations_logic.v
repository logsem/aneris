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
  Context {oGS: @asem_GS _ _ ASEM Σ}. 
  
  Section BMU.

    Definition OAM_st_interp_interim_step (c c': cfg heap_lang)
      (δ: amSt OAM) (τ: locale heap_lang) (k: nat) oτ': iProp Σ :=
          ∃ δ__k,
            obls_msi δ__k (oGS := oGS) ∗
            ⌜ nsteps (fun p1 p2 => loc_step_ex p1 p2) k δ δ__k ⌝ ∗
            ⌜ threads_own_obls c δ ⌝ ∗
            ⌜ dom_phases_obls δ ⌝ ∗
            ⌜ dom_obls_eq (dom $ ps_obls δ) δ__k ⌝ ∗
           ⌜ locale_step c (Some τ) c' ⌝ ∗
           ⌜ step_fork c c' = oτ' ⌝
    .


    Definition BMU E (* ζ *) b (P : iProp Σ) : iProp Σ :=
      ∀ c c' δ ζ n f,
      OAM_st_interp_interim_step c c' δ ζ n f ={E}=∗
      ∃ n', OAM_st_interp_interim_step c c' δ ζ n' f ∗ 
            ⌜ n' - n <= b ⌝ ∗
            P.

    Lemma finish_obls_steps c c' δ τ n π' deg
      (BOUND: n <= LIM_STEPS)
      (LE: exists π, ps_phases δ !! τ = Some π /\ phase_le π' π)
      :
      ⊢ OAM_st_interp_interim_step c c' δ τ n None -∗ (cp π' deg (oGS := oGS))==∗
        ∃ δ', obls_si c' δ' (ObligationsGS0 := oGS) ∗ ⌜ om_trans δ τ δ' ⌝
    .
    Proof.
      iIntros "TI'' cp".
      rewrite /OAM_st_interp_interim_step.

      iDestruct "TI''" as (δ__k) "(MSI&%TRANSS&%TH_OWN&%DPO&%OBLS&%STEP&%NOFORK)".
      iDestruct (cp_msi_dom with "[$] [$]") as %CP.
      destruct LE as (π__max & PH & LE0).
      
      iMod (burn_cp_upd_impl with "[$] [$]") as "X".
      { eexists. split; eauto.
        rewrite -PH.
        unshelve eapply (pres_by_loc_step_implies_rep _ _ _ _ _) in TRANSS.
        { eapply loc_step_phases_pres. }
        3: reflexivity.
        2: { rewrite TRANSS. reflexivity. } 
      }
      iDestruct "X" as "(%δ' & MSI & %BURNS)". 
      iModIntro. iExists _. simpl. iFrame.
      
      assert (threads_own_obls c' δ') as TH_OWN'.
      { eapply locale_nofork_step_obls_pres; eauto.
        2: { apply gset_pick_None in NOFORK.
             apply set_eq_subseteq. split.
             - apply empty_difference_subseteq_L in NOFORK. set_solver. 
             - eapply locale_step_sub; eauto. }
        red. eexists. split; [eauto| ].
        eexists. split; eauto. }
      
      iPureIntro. split; [split| ]; auto.
      - eapply pres_by_loc_step_implies_progress; eauto.
        { apply loc_step_dpo_pres. }
        do 2 (eexists; split; eauto).
      - simpl. red. eexists. split; eauto.
        + eexists. split; eauto. eexists. split; eauto.
        + by right.
    Qed.

    Lemma finish_obls_steps_fork c c' δ  τ τ' n π' π deg R0 R' 
      (BOUND: n <= LIM_STEPS)
      (* can use th_phase_ge here, since it'll only be used after BMU *)
      (* TODO: unify these proofs? *)
      (* (LE: exists π, ps_phases (trace_last omtr) !! τ = Some π /\ phase_le π' π) *)
      (LE: phase_le π' π)
      :
      ⊢ OAM_st_interp_interim_step c c' δ τ n (Some τ') -∗ (cp π' deg (oGS := oGS)) -∗ obls τ R0 (oGS := oGS) -∗ th_phase_eq τ π (oGS := oGS) ==∗
        ∃ δ' π1 π2,
          obls_si c' δ' (ObligationsGS0 := oGS) ∗
          obls τ (R0 ∖ R') (oGS := oGS) ∗ th_phase_eq τ π1 (oGS := oGS) ∗ 
          obls τ' (R0 ∩ R') (oGS := oGS) ∗ th_phase_eq τ' π2 (oGS := oGS) ∗
          ⌜ phase_lt π π1 /\ phase_lt π π2 ⌝ ∗ ⌜ om_trans δ τ δ' ⌝.
    Proof using.
      clear H1 H0 H. 

      iIntros "TI'' cp OB PH".
      rewrite /OAM_st_interp_interim_step.
      
      iDestruct "TI''" as (δ__k) "(MSI&%TRANSS&%TH_OWN&%DPO&%OBLS&%STEP&%FORK)".
      iDestruct (cp_msi_dom with "[$] [$]") as %CP.
      
      apply gset_pick_Some in FORK. 
      eapply locale_step_fresh_exact in FORK; eauto.  
      destruct FORK as (LOCS' & FRESH).

      (* iDestruct (th_phase_msi_ge with "[$] [$]") as %(π__max & PH & LE0). *)
      iDestruct (th_phase_msi_eq_strong with "[$] [$]") as "(MSI & PH & %PH)".
      
      iMod (burn_cp_upd_impl with "[$] [$]") as "X".
      { eexists. split; eauto. }
      iDestruct "X" as "(%δ' & MSI & %BURNS)".

      assert (dom_obls_eq (dom (ps_obls δ)) δ') as OBLS'.
      { eapply pres_by_loc_step_implies_progress.
        { apply loc_step_dom_obls_pres. }
        { reflexivity. }
        eexists. do 2 (esplit; eauto). }
      assert (dom_phases_obls δ') as DPO'.
      { eapply pres_by_loc_step_implies_progress; eauto.
        { apply loc_step_dpo_pres. }
        eexists. do 2 (esplit; eauto). }
       
      iMod (fork_locale_upd_impl with "[$] [$] [$]") as "Y"; eauto. 
      { rewrite DPO'. rewrite OBLS'.
        rewrite -TH_OWN. apply FRESH. }
      iDestruct "Y" as "(%δ'' & %π1 & %π2 & MSI & PH1 & PH3 & OB1 & OB2 & %FORKS & [%LT1 %LT2])".
      
      iModIntro. do 3 iExists _. simpl. iFrame.

      (* TODO: make a lemma? *)
      assert (dom (ps_obls δ'') = dom (ps_obls δ') ∪ {[ τ' ]}) as OBLS''.
      { inversion FORKS. subst. subst ps'.
        destruct δ'. simpl. subst new_obls0. simpl in *.
        rewrite !dom_insert_L.
        enough (τ ∈ dom ps_obls).
        { clear -H. set_solver. }
        rewrite -DPO'. simpl. eapply elem_of_dom; eauto. }
      (* TODO: make a lemma? *)
      assert (dom (ps_phases δ'') = dom (ps_phases δ') ∪ {[ τ' ]}) as PHASES''.
      { inversion FORKS. subst. subst ps'.
        destruct δ'. simpl. subst new_phases0. simpl in *.
        rewrite !dom_insert_L.
        enough (τ ∈ dom ps_phases).
        { clear -H. set_solver. }
        eapply elem_of_dom; eauto. }
      
      iPureIntro.
      do 2 split; auto.
      - red. rewrite LOCS'.
        rewrite OBLS''. f_equal. set_solver.
      - red. rewrite OBLS'' PHASES''. f_equal.
        done. 
      - eexists. split; eauto.
        + eexists. split; eauto. eexists. split; eauto.
        + left. red. eauto.
    Qed.
      
    Lemma BMU_intro E b (P : iProp Σ):
      ⊢ P -∗ BMU E b P.
    Proof using. 
      rewrite /BMU. iIntros "**". iModIntro.
      iExists _. iFrame. iPureIntro. lia.
    Qed. 

    Global Instance BMU_proper:
      Proper (equiv ==> eq ==> equiv ==> equiv) BMU.
    Proof using. solve_proper. Qed. 

    Lemma BMU_frame E b (P Q : iProp Σ):
      ⊢ P -∗ BMU E b Q -∗ BMU E b (P ∗ Q).
    Proof using. 
      rewrite /BMU. iIntros "P BMU **".
      iMod ("BMU" with "[$]") as "(%&?&?&?)". iModIntro. 
      iExists _. iFrame.
    Qed.

    Lemma BMU_weaken E1 E2 m1 m2 P1 P2
      (LE: m1 <= m2)
      (SUB: E1 ⊆ E2):
      ⊢ (P1 -∗ P2) -∗ BMU E1 m1 P1 -∗ BMU E2 m2 P2.
    Proof using.
      rewrite /BMU.
      iIntros "IMPL BMU". iIntros "**".
      iApply fupd_mask_mono; [apply SUB| ].
      iMod ("BMU" with "[$]") as (?) "(? & % & ?)". iModIntro.
      iExists _. iFrame. iSplitR.
      { iPureIntro. lia. }
      by iApply "IMPL".
    Qed.

    Lemma BMU_wand E b (P Q : iProp Σ):
      ⊢ (P -∗ Q) -∗ BMU E b P -∗ BMU E b Q.
    Proof using.
      iIntros "**". by iApply (BMU_weaken with "[$]"). 
    Qed.

    Lemma BMU_lower E m n P (LE: m <= n):
      ⊢ BMU E m P -∗ BMU E n P.
    Proof using.
      clear -LE OM. 
      iIntros "**". iApply (BMU_weaken); try done. set_solver. 
    Qed.

    Lemma BMU_AMU E ζ b (P : iProp Σ) π
      (BOUND: b <= LIM_STEPS)
      :
      ⊢ (th_phase_eq ζ π (oGS := oGS) -∗ BMU E b ((P) ∗ ∃ ph deg, cp ph deg (oGS := oGS) ∗ ⌜ phase_le ph π ⌝)) -∗
        th_phase_eq ζ π (oGS := oGS) -∗
        AMU E ζ obls_act P (aeGS := oGS).
    Proof using.
      rewrite /AMU /AMU_impl /BMU. iIntros "BMU PH" (c c' δ) "TI'".

      rewrite /AM_st_interp_interim.
      iDestruct "TI'" as "(MSI&%STEP&%FORK)". iFrame. 

      (* iDestruct (th_phase_msi_ge with "[MSI] [$]") as %(π__max & PH & LE0). *)
      iDestruct "MSI" as "(MSI&%OBLS&%DPO)".
      iDestruct (th_phase_msi_eq_strong with "[$] [$]") as "(MSI & PH & %PH)".
      (* { rewrite /AM_st_interp_interim. *)
      (*   simpl. iDestruct "TI'" as "((?&?&?)&?&?)". iFrame. } *)
      iSpecialize ("BMU" with "[$]").
      iSpecialize ("BMU" $! c c' δ ζ 0 None with "[MSI]").
      { rewrite /OAM_st_interp_interim_step /AM_st_interp_interim.
        iExists _. iFrame. iPureIntro.
        repeat split; try done.
        by apply nsteps_0.         
      }
      iMod "BMU" as (n') "(TI'' & %BOUND' & P & (%ph & %deg & CP & %PH'))".
      iMod (finish_obls_steps with "[$] [$]") as (?) "(SI & %TRANS)".
      { lia. }
      { eexists. split; [apply PH| ].
        red. etrans; eauto. }
      rewrite /obls_si. iDestruct "SI" as "(SI & %TH_OWN' & %DPO')". 
      iModIntro. iExists δ', (Some ζ). iFrame. 
      iFrame. iPureIntro. split; [done| ].
      simpl. split; [| done]. red.
      repeat split; auto. 
    Qed.

    Lemma BMU_AMU__f E ζ ζ' b (P : iProp Σ) π R0 R'
      (BOUND: b <= LIM_STEPS)
      :
      ⊢ (th_phase_eq ζ π (oGS := oGS) -∗ BMU E b
           (P ∗ (∃ ph deg, cp ph deg (oGS := oGS) ∗ ⌜ phase_le ph π ⌝) ∗
           th_phase_eq ζ π (oGS := oGS) ∗
           obls ζ R0 (oGS := oGS))) -∗
        th_phase_eq ζ π (oGS := oGS) -∗
        AMU__f E ζ ζ' obls_act (P ∗ ∃ π1 π2, 
                     th_phase_eq ζ π1 (oGS := oGS) ∗ obls ζ (R0 ∖ R') (oGS := oGS) ∗
                     th_phase_eq ζ' π2 (oGS := oGS) ∗ obls ζ' (R0 ∩ R') (oGS := oGS) ∗
                     ⌜ phase_lt π π1 /\ phase_lt π π2 ⌝
        ) (aeGS := oGS).
    Proof using.
      clear H1 H0 H. 
      rewrite /AMU__f /AMU_impl /BMU. iIntros "BMU PH" (c c' δ) "TI'".
      iDestruct "TI'" as "(MSI&%STEP&%FORK)". iFrame. 
      iDestruct "MSI" as "(MSI&%OBLS&%DPO)".
      iDestruct (th_phase_msi_eq_strong with "[$] [$]") as "(MSI & PH & %PH)".
      iSpecialize ("BMU" with "[$]").
      iSpecialize ("BMU" $! c c' δ ζ 0 (Some ζ') with "[MSI]").
      { rewrite /OAM_st_interp_interim_step /AM_st_interp_interim.
        iExists _. iFrame. iPureIntro.
        repeat split; try done.
        by constructor. }
      iMod "BMU" as (n') "(TI'' & %BOUND' & P & (%ph & %deg & CP & %PH') & PH & OB )".
      iMod (finish_obls_steps_fork with "[$] [$] [$] [$]") as (?) "SI".
      { lia. }
      { done. }
      iDestruct "SI" as (π1 π2) "(SI & OB1 & PH1 & OB2 & PH3 & ((%PH1 & %PH2) & %TRANS))".
      rewrite /obls_si. iDestruct "SI" as "(SI&%CORR')". iFrame.
      iModIntro. iExists _, _. iFrame.
      iSplitR; [done| ].
      iSplitR. 
      2: { do 2 iExists _. iFrame. done. }
      simpl. Unshelve. 2: exact (Some ζ). done. 
    Qed.

    Lemma BMU_split E P n m:
       ⊢ BMU E n (BMU E m P) -∗ BMU E (n + m) P.
    Proof using.
      iIntros "BMU1".
      rewrite {1}/BMU. 
      iIntros (c c' δ τ k f) "TI'".
      iMod ("BMU1" with "[$]") as (t) "(TI' & %LE & BMU')".
      iMod ("BMU'" with "[$]") as (v) "(TI' & %LE' & P)".
      iModIntro. iExists _. iFrame. iPureIntro. lia. 
    Qed.

    (* TODO: derive as consequence of BMU_split *)
    Lemma OU_BMU E P b:
       ⊢ OU (BMU E b P) (oGS := oGS) -∗ BMU E (S b) P.
    Proof using.
      iIntros "OU". rewrite {2}/BMU /OAM_st_interp_interim_step.
      iIntros (c c' δ τ n f) "TI'".
      iDestruct "TI'" as "(%δ_ & MSI & %TRANS1 & %TH_OWN & %DPO & %OBLS_EQ & %STEP & %FF)".
      rewrite /OU. iMod ("OU" with "[$]") as "(%δ' & MSI & %TRANS2 & CONT)".
      
      iSpecialize ("CONT" $! c c' δ with "[MSI]").
      { rewrite /OAM_st_interp_interim_step. iExists _. iFrame.
        iPureIntro. repeat split; eauto.
        - eapply rel_compose_nsteps_next. eexists. split; eauto.
        - eapply loc_step_dom_obls_pres; eauto. }
      iMod "CONT" as "(%n' & TI' & %BOUND' & P)". iModIntro.
      rewrite FF. 
      iExists _. iFrame. iSplitL.
      - simpl. iDestruct "TI'" as (xx) "(?&?&?&?&?&?&?)".
        iExists _. iFrame. iPureIntro. done.
      - iPureIntro. lia. 
    Qed.

    (* an example usage of OU *)
    Lemma BMU_step_create_signal E ζ P b l R:
       ⊢ (∀ sid, sgn sid l (Some false) (oGS := oGS) -∗ obls ζ (R ∪ {[ sid ]}) (oGS := oGS) -∗ BMU E b P) -∗ obls ζ R (oGS := oGS) -∗ BMU E (S b) P.
    Proof using.
      iIntros "CONT OB".
      iApply OU_BMU. iApply (OU_wand with "[CONT]").
      { setoid_rewrite bi.wand_curry. rewrite -bi.exist_wand_forall.
        iFrame. }
      iPoseProof (OU_create_sig with "OB") as "OU".
      iApply (OU_wand with "[-OU] [$]").
      iIntros "(%&?&?&?)". iExists _. iFrame. 
    Qed. 

  End BMU.

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
  Context `{oGS: @asem_GS _ _ ASEM Σ}.

  Hypothesis (LIM_STEPS_LB: 5 <= LIM_STEPS).

  Context `{EM: ExecutionModel heap_lang M}. 
  Context `{hGS: @heapGS Σ _ EM}.

  Context {OBLS_AMU: @AMU_lift_MU _ _ _ oGS _ EM _ (↑ nroot)}.
  Context {OBLS_AMU__f: forall τ, @AMU_lift_MU__f _ _ _ τ oGS _ EM _ (↑ nroot)}.
 
  Context {NO_OBLS_POST: ⊢ ∀ τ, obls τ ∅ (oGS := oGS) -∗ 
                                  em_thread_post τ (em_GS0 := heap_fairnessGS (heapGS := hGS))}.

  Lemma test_spec (τ: locale heap_lang) (π: Phase) (d d': Degree) (l: Level)
    (DEG: deg_lt d' d)
    :
    {{{ cp_mul π d 10 (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗ obls τ ∅ (oGS := oGS) ∗ exc_lb 5 (oGS := oGS) }}}
      test_prog @ τ
      {{{ x, RET #x; obls τ ∅ (oGS := oGS) }}}.
  Proof.
    iIntros (Φ). iIntros "(CPS & PH & OBLS & #EB) POST".
    rewrite /test_prog. 

    wp_bind (_ + _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step; [done| ].
    rewrite /Z.add. simpl. 
    iNext.
    iApply OBLS_AMU; [by rewrite nclose_nroot| ].

    iApply (BMU_AMU with "[-PH] [$]"); [eauto| ]. iIntros "PH".
    iApply OU_BMU.
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
    iDestruct (exchange_cp_upd with "[$] [$] [$]") as "OU"; eauto.
    { done. }
    iApply (OU_wand with "[-OU]"); [| done].
    iIntros "[CPS' PH]". 
    iApply BMU_intro.
    iDestruct (cp_mul_take with "CPS'") as "[CPS' CP']". 
    iSplitR "CP'".
    2: { do 2 iExists _. iFrame. iPureIntro.
         red. reflexivity. }

    iApply wp_value.

    wp_bind (ref _)%E. 
    iApply sswp_MU_wp; [done| ].
    iApply wp_alloc. iIntros "!> %x L ?".
    iApply OBLS_AMU; [by rewrite nclose_nroot| ].
    iApply (BMU_AMU with "[-PH] [$]"); [eauto| ]. iIntros "PH".
    iApply OU_BMU.
    iDestruct (OU_create_sig _ _ l with "[$]") as "OU".
    iApply (OU_wand with "[-OU]"); [| done].
    iIntros "(%sid & SIG & OBLS & %NEW)".
    iApply BMU_intro.
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
    iSplitR "CP". 
    2: { do 2 iExists _. iFrame. iPureIntro.
         red. reflexivity. }

    iApply wp_value.

    wp_bind (Rec _ _ _). 
    iApply sswp_MU_wp; [done| ].      
    iApply sswp_pure_step; [done| ].
    iNext. iApply OBLS_AMU; [by rewrite nclose_nroot| ].
    iApply (BMU_AMU with "[-PH] [$]"); [eauto| ]. iIntros "PH".
    iApply BMU_intro.
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
    iSplitR "CP".
    2: { do 2 iExists _. iFrame. iPureIntro.
         red. reflexivity. }
    rewrite union_empty_l_L. 

    iApply wp_value. 

    iApply sswp_MU_wp; [done| ].      
    iApply sswp_pure_step; [done| ].
    iNext. iApply OBLS_AMU; [by rewrite nclose_nroot| ].
    iApply (BMU_AMU with "[-PH] [$]"); [eauto| ]. iIntros "PH".
    iApply BMU_intro.
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
    iSplitR "CP". 
    2: { do 2 iExists _. iFrame. iPureIntro.
         red. reflexivity. }

    simpl.

    iApply sswp_MUf_wp. iIntros (τ'). iApply (MU__f_wand with "[]").
    2: {
      iApply OBLS_AMU__f; [by rewrite nclose_nroot| ]. 
      iApply (BMU_AMU__f with "[-PH]"); [apply LIM_STEPS_LB| ..].
      2: by iFrame.
      iIntros "PH".
      
      iApply OU_BMU.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
      iApply (OU_wand with "[-CP PH]"). 
      2: { iApply (burn_cp_upd with "CP [$]"). done. }
      iIntros "PH".
      
      iApply BMU_intro. iFrame "PH OBLS".
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
      iSplitR "CP".
      2: { do 2 iExists _. iFrame. iPureIntro. reflexivity. }
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
      iApply (BMU_AMU with "[-PH3] [$]"); [eauto| ]. iIntros "PH3".
      iApply OU_BMU.
      iDestruct (OU_set_sig with "OB2 SIG") as "OU"; [set_solver| ].
      iApply (OU_wand with "[-OU]"); [| done].
      iIntros "[SIG OB2]". 
      iApply BMU_intro.
      iDestruct (cp_mul_take with "CPS'") as "[CPS' CP]".
      iSplitR "CP".
      2: { do 2 iExists _. iFrame. iPureIntro. apply LT2. }

      iApply wp_value.
      simpl.
      iApply NO_OBLS_POST. 
      iApply (obls_proper with "[$]").
      set_solver.
  Qed. 

End TestProg.
