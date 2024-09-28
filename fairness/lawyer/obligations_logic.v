From iris.proofmode Require Import tactics coq_tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From trillium.fairness Require Import locales_helpers utils. 
From trillium.fairness.lawyer Require Import obligations_model obls_utils obligations_resources obligations_em program_logic.
From trillium.fairness.heap_lang Require Export heap_lang_defs tactics notation sswp_logic locales_helpers_hl.


Close Scope Z. 

Section ProgramLogic.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.
  
  Context `(OP: ObligationsParams Degree Level (locale heap_lang) LIM_STEPS).
  Let OM := ObligationsModel OP.
  
  Let EM := ObligationsEM OP. 

  Context `{hGS: @heapGS Σ _ EM}.

  Let oGS : ObligationsGS OP Σ := heap_fairnessGS (heapGS := hGS).

  Section BMU.

    Definition HL_OM_trace_interp'_step (extr: execution_trace heap_lang)
      (omtr: auxiliary_trace OM) (τ: locale heap_lang) (k: nat) (oτ': option (locale heap_lang)): iProp Σ :=
      match extr with
      | {tr[ _ ]} => False
      | extr' :tr[oζ]: c' =>
          let c := trace_last extr' in
          let δ := trace_last omtr in
          ∃ δ__k,
            gen_heap_interp c'.2.(heap) ∗
            obls_msi OP δ__k (H3 := oGS) ∗
            ⌜ nsteps (fun p1 p2 => loc_step OP p1 τ p2) k δ δ__k  ⌝ ∗
            ⌜ threads_own_obls OP c δ ⌝ ∗
            ⌜ dom_phases_obls OP δ ⌝ ∗
            ⌜ obls_eq OP δ__k (dom $ ps_obls OP δ) ⌝ ∗
            ⌜ oζ = Some τ ⌝ ∗
           ⌜ locale_step c (Some τ) c' ⌝ ∗ 
           ⌜ extr_last_fork $ extr' :tr[oζ]: c' = oτ' ⌝
      end. 

    Definition BMU E ζ b (P : iProp Σ) : iProp Σ :=
    ∀ extr atr n f,
      HL_OM_trace_interp'_step extr atr ζ n f ={E}=∗
      ∃ n', HL_OM_trace_interp'_step extr atr ζ n' f ∗ 
            ⌜ n' - n <= b ⌝ ∗
            P.

    Lemma finish_obls_steps extr omtr τ n π' deg
      (BOUND: n <= LIM_STEPS)
      (LE: exists π, ps_phases OP (trace_last omtr) !! τ = Some π /\ phase_le π' π)
      :
      ⊢ HL_OM_trace_interp'_step extr omtr τ n None -∗ (cp OP π' deg (H3 := oGS))==∗
        ∃ δ', state_interp extr (trace_extend omtr τ δ') (irisG := @heapG_irisG _ _ _ hGS).
    Proof.
      iIntros "TI'' cp".
      rewrite /HL_OM_trace_interp'_step.

      destruct extr; [done| ].
      iDestruct "TI''" as (δ__k) "(HEAP&MSI&%TRANSS&%TH_OWN&%DPO&%OBLS&->&%STEP&%NOFORK)".
      iDestruct (cp_msi_dom with "[$] [$]") as %CP.
      destruct LE as (π__max & PH & LE0).
      
      iMod (burn_cp_upd_impl with "[$] [$]") as "X".
      { eexists. split; eauto.
        rewrite -PH.
        (* TODO: use stricter version of progress_step_dpo_pres for nsteps *)
        erewrite loc_step_nsteps_phases_pres; eauto.
        apply phases_eq_init. }
      iDestruct "X" as "(%δ' & MSI & %BURNS)". 
      iModIntro. iExists _. simpl. iFrame.
      
      assert (threads_own_obls OP a δ') as TH_OWN'.
      { eapply locale_nofork_step_obls_pres; eauto.
        2: { apply gset_pick_None in NOFORK.
             apply set_eq_subseteq. split.
             - apply empty_difference_subseteq_L in NOFORK. set_solver. 
             - eapply locale_step_sub; eauto. }
        red. eexists. split; [eauto| ].
        eexists. split; eauto. }
      
      iPureIntro. do 2 split; auto.
      - red. repeat split; auto.
        simpl. red. eexists. split; eauto.
        + eexists. split; eauto. eexists. split; eauto.
        + by right. 
      - eapply progress_step_dpo_pres; eauto.
        do 2 (eexists; split; eauto). 
    Qed.  

    Lemma finish_obls_steps_fork extr omtr τ τ' n π' π deg R0 R' 
      (BOUND: n <= LIM_STEPS)
      (* can use th_phase_ge here, since it'll only be used after BMU *)
      (* TODO: unify these proofs? *)
      (* (LE: exists π, ps_phases OP (trace_last omtr) !! τ = Some π /\ phase_le π' π) *)
      (LE: phase_le π' π)
      :
      ⊢ HL_OM_trace_interp'_step extr omtr τ n (Some τ') -∗ (cp OP π' deg (H3 := oGS)) -∗ obls OP τ R0 (H3 := oGS) -∗ th_phase_ge OP τ π (H3 := oGS) ==∗
        ∃ δ' π1 π2,
          state_interp extr (trace_extend omtr τ δ') (irisG := @heapG_irisG _ _ _ hGS) ∗
          obls OP τ (R0 ∖ R') (H3 := oGS) ∗ th_phase_ge OP τ π1 (H3 := oGS) ∗ 
          obls OP τ' R' (H3 := oGS) ∗ th_phase_ge OP τ' π2 (H3 := oGS) ∗
          ⌜ phase_lt π π1 /\ phase_lt π π2 ⌝.
    Proof.
      iIntros "TI'' cp OB PH".
      rewrite /HL_OM_trace_interp'_step.
      destruct extr; [done| ].
      
      iDestruct "TI''" as (δ__k) "(HEAP&MSI&%TRANSS&%TH_OWN&%DPO&%OBLS&->&%STEP&%FORK)".
      iDestruct (cp_msi_dom with "[$] [$]") as %CP.
      
      apply gset_pick_Some in FORK. 
      eapply locale_step_fresh_exact in FORK; eauto.  
      destruct FORK as (LOCS' & FRESH).

      (* destruct LE as (π__max & PH & LE0). *)
      iDestruct (th_phase_msi_ge with "[$] [$]") as %(π__max & PH & LE0).
      
      iMod (burn_cp_upd_impl with "[$] [$]") as "X".
      { eexists. split; eauto.
        red. etrans; eauto. }
      iDestruct "X" as "(%δ' & MSI & %BURNS)".

      assert (obls_eq OP δ' (dom (ps_obls OP (trace_last omtr)))) as OBLS'.
      { eapply (progress_step_obls_pres _ (trace_last omtr)); eauto.
        2: done. 
        eexists. do 2 (esplit; eauto). }
      assert (dom_phases_obls OP δ') as DPO'.
      { eapply progress_step_dpo_pres; eauto.
        eexists. do 2 (esplit; eauto). }
       
      iMod (fork_locale_upd_impl with "[$] [$] [$]") as "Y"; eauto. 
      { rewrite DPO'. rewrite OBLS'.
        rewrite -TH_OWN. apply FRESH. }
      iDestruct "Y" as "(%δ'' & %π1 & %π2 & MSI & PH1 & PH3 & OB1 & OB2 & %FORKS & [%LT1 %LT2])".
      
      iModIntro. do 3 iExists _. simpl. iFrame.

      (* TODO: make a lemma? *)
      assert (dom (ps_obls OP δ'') = dom (ps_obls OP δ') ∪ {[ τ' ]}) as OBLS''.
      { inversion FORKS. subst. subst ps'.
        destruct δ'. simpl. subst new_obls0. simpl in *.
        rewrite !dom_insert_L.
        enough (τ ∈ dom ps_obls).
        { clear -H2. set_solver. }
        rewrite -DPO'. simpl. eapply elem_of_dom; eauto. }
      (* TODO: make a lemma? *)
      assert (dom (ps_phases OP δ'') = dom (ps_phases OP δ') ∪ {[ τ' ]}) as PHASES''.
      { inversion FORKS. subst. subst ps'.
        destruct δ'. simpl. subst new_phases0. simpl in *.
        rewrite !dom_insert_L.
        enough (τ ∈ dom ps_phases).
        { clear -H2. set_solver. }
        eapply elem_of_dom; eauto. }
      
      iPureIntro.
      split.
      2: { split; [apply LT1| apply LT2]. } 
      do 2 split; auto.
      - red. repeat split; auto.
        simpl. red. eexists. split; eauto.
        + eexists. split; eauto. eexists. split; eauto.
        + left. eauto. 
      - red. rewrite LOCS'.
        rewrite OBLS''. f_equal. set_solver.
      - red. rewrite OBLS'' PHASES''. f_equal.
        done. 
    Qed. 
      
    Lemma BMU_intro E ζ b (P : iProp Σ):
      ⊢ P -∗ BMU E ζ b P.
    Proof. 
      rewrite /BMU. iIntros "**". iModIntro.
      iExists _. iFrame. iPureIntro. lia.
    Qed. 

    Lemma BMU_frame E ζ b (P Q : iProp Σ):
      ⊢ P -∗ BMU E ζ b Q -∗ BMU E ζ b (P ∗ Q).
    Proof. 
      rewrite /BMU. iIntros "P BMU **".
      iMod ("BMU" with "[$]") as "(%&?&?&?)". iModIntro. 
      iExists _. iFrame.
    Qed.

    Lemma BMU_wand E ζ b (P Q : iProp Σ):
      ⊢ (P -∗ Q) -∗ BMU E ζ b P -∗ BMU E ζ b Q.
    Proof. 
      rewrite /BMU. iIntros "PQ BMU **".
      iMod ("BMU" with "[$]") as "(%&?&?&?)". iModIntro. 
      iExists _. iFrame. by iApply "PQ". 
    Qed.

    Lemma BMU_lower E ζ m n P (LE: m <= n):
      ⊢ BMU E ζ m P -∗ BMU E ζ n P.
    Proof. 
      rewrite /BMU.
      iIntros "BMU". iIntros "**". 
      iMod ("BMU" with "[$]") as (?) "(? & % & ?)". iModIntro.
      iExists _. iFrame. iPureIntro. lia.
    Qed.

    Lemma BMU_MU E ζ b (P : iProp Σ) π
      (BOUND: b <= LIM_STEPS)
      :
      ⊢ (th_phase_ge OP ζ π (H3 := oGS) -∗ BMU E ζ b ((P) ∗ ∃ ph deg, cp OP ph deg (H3 := oGS) ∗ ⌜ phase_le ph π ⌝)) -∗
        th_phase_ge OP ζ π (H3 := oGS) -∗
        MU E ζ P (hGS := hGS).
    Proof.
      rewrite /MU /BMU. iIntros "BMU PH" (etr otr) "TI'".      
      iDestruct (th_phase_msi_ge with "[TI'] [$]") as %(π__max & PH & LE0).
      { rewrite /trace_interp_interim. destruct etr; [done| ].
        iDestruct "TI'" as "(?&SI&->&%&?)".
        iDestruct "SI" as "(?&?&?)". 
        iFrame. }
      iSpecialize ("BMU" with "[$]").
      iSpecialize ("BMU" $! etr otr 0 None with "[TI']").
      { rewrite /trace_interp_interim /HL_OM_trace_interp'_step.
        destruct etr; [done| ].
        iDestruct "TI'" as "(HEAP&(MSI&%OBLS&%DPO)&->&%STEP&%NOFORK)".
        iExists _. iFrame. iPureIntro.
        repeat split; try done.
        by constructor. }
      iMod "BMU" as (n') "(TI'' & %BOUND' & P & (%ph & %deg & CP & %PH'))".
      iMod (finish_obls_steps with "[$] [$]") as (?) "SI".
      { lia. }
      { eexists. split; [apply PH| ].
        red. etrans; eauto. }
      iFrame.
      iModIntro. eauto.
    Qed.

    Lemma BMU_MU__f E ζ ζ' b (P : iProp Σ) π R0 R'
      (BOUND: b <= LIM_STEPS)
      :
      ⊢ (th_phase_ge OP ζ π (H3 := oGS) -∗ BMU E ζ b
           (P ∗ (∃ ph deg, cp OP ph deg (H3 := oGS) ∗ ⌜ phase_le ph π ⌝) ∗
           th_phase_ge OP ζ π (H3 := oGS) ∗
           obls OP ζ R0 (H3 := oGS))) -∗
        th_phase_ge OP ζ π (H3 := oGS) -∗
        MU__f E ζ ζ' (P ∗ ∃ π1 π2, 
                     th_phase_ge OP ζ π1 (H3 := oGS) ∗ obls OP ζ (R0 ∖ R') (H3 := oGS) ∗
                     th_phase_ge OP ζ' π2 (H3 := oGS) ∗ obls OP ζ' R' (H3 := oGS) ∗
                     ⌜ phase_lt π π1 /\ phase_lt π π2 ⌝
        ) (hGS := hGS).
    Proof.
      rewrite /MU__f /MU_impl /BMU. iIntros "BMU PH" (etr otr) "TI'".      
      iDestruct (th_phase_msi_ge with "[TI'] [$]") as %(π__max & PH & LE0).
      { rewrite /trace_interp_interim. destruct etr; [done| ].
        iDestruct "TI'" as "(?&(?&?&?)&?&?)". iFrame. }
      iSpecialize ("BMU" with "[$]").
      iSpecialize ("BMU" $! etr otr 0 (Some ζ') with "[TI']").
      { rewrite /trace_interp_interim /HL_OM_trace_interp'_step.
        destruct etr; [done| ].
        iDestruct "TI'" as "(HEAP&(MSI&%OBLS&%DPO)&->&%STEP&%NOFORK)".
        iExists _. iFrame. iPureIntro.
        repeat split; try done.
        by constructor. }
      iMod "BMU" as (n') "(TI'' & %BOUND' & P & (%ph & %deg & CP & %PH') & PH & OB )".
      iMod (finish_obls_steps_fork with "[$] [$] [$] [$]") as (?) "SI".
      { lia. }
      { done. }
      iDestruct "SI" as (π1 π2) "(SI & OB1 & PH1 & OB2 & PH3)".
      iModIntro. iExists _, _. iFrame "P SI". iFrame.
      do 2 iExists _. iFrame.  
    Qed.

    Lemma OU_BMU E ζ P b:
       ⊢ OU OP ζ (BMU E ζ b P) (H3 := oGS) -∗ BMU E ζ (S b) P.
    Proof.
      iIntros "OU". rewrite {2}/BMU /HL_OM_trace_interp'_step.
      iIntros (etr atr n f) "TI'". destruct etr; [done| ].
      iDestruct "TI'" as "(%δ & HEAP & MSI & %TRANS1 & %TH_OWN & %DPO & %OBLS_EQ & -> & %STEP & %FF)".
      rewrite /OU. iMod ("OU" with "[$]") as "(%δ' & MSI & %TRANS2 & CONT)".
      iSpecialize ("CONT" $! (etr :tr[ _ ]: _) with "[HEAP MSI]").
      { rewrite /HL_OM_trace_interp'_step. iExists _.  iFrame.
        iPureIntro. repeat split; eauto.
        - eapply rel_compose_nsteps_next. eexists. split; eauto.
        - eapply loc_step_obls_pres; eauto. }
      iMod "CONT" as "(%n' & TI' & %BOUND' & P)". iModIntro.
      rewrite FF. 
      iExists _. iFrame. iSplitL.
      - simpl. iDestruct "TI'" as (xx) "(?&?&?&?&?&?&?)".
        iExists _. iFrame. iPureIntro. done.
      - iPureIntro. lia. 
    Qed.

    (* an example usage of OU *)
    Lemma BMU_step_create_signal E ζ P b l R:
       ⊢ (∀ sid, sgn OP sid l (Some false) (H3 := oGS) -∗ obls OP ζ (R ∪ {[ sid ]}) (H3 := oGS) -∗ BMU E ζ b P) -∗ obls OP ζ R (H3 := oGS) -∗ BMU E ζ (S b) P.
    Proof.
      iIntros "CONT OB".
      iApply OU_BMU. iApply (OU_wand with "[CONT]").
      { setoid_rewrite bi.wand_curry. rewrite -bi.exist_wand_forall.
        iFrame. }
      iPoseProof (OU_create_sig with "OB") as "OU". done.
    Qed. 

  End BMU.

  Section TestProg.
    
    Let test_prog: expr :=
          let: "x" := ref (#1 + #1) in
          Fork(!"x")
    .

    Hypothesis (LIM_STEPS_LB: 5 <= LIM_STEPS).

    Lemma obls_proper ζ R1 R2 (EQUIV: R1 ≡ R2):
      ⊢ obls OP ζ R1 (H3 := oGS) ∗-∗ obls OP ζ R2 (H3 := oGS).
    Proof. set_solver. Qed. 


    Lemma test_spec (τ: locale heap_lang) (π: Phase) (d d': Degree) (l: Level)
      (DEG: opar_deg_lt d' d)
      :
      {{{ cp_mul OP π d 10 (H3 := oGS) ∗ th_phase_ge OP τ π (H3 := oGS) ∗ obls OP τ ∅ (H3 := oGS) ∗ exc_lb OP 5 (H3 := oGS) }}}
        test_prog @ τ
      {{{ x, RET #x; obls OP τ ∅ (H3 := oGS) }}}.
    Proof.
      iIntros (Φ). iIntros "(CPS & PH & OBLS & #EB) POST".
      rewrite /test_prog. 

      wp_bind (_ + _)%E.
      iApply sswp_MU_wp; [done| ].
      iApply sswp_pure_step; [done| ].
      rewrite /Z.add. simpl. 
      iNext. iApply (BMU_MU with "[-PH] [$]"); [eauto| ]. iIntros "PH".
      iApply OU_BMU.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
      iDestruct (exchange_cp_upd with "[$] [$] [$]") as "OU"; eauto.
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
      iApply (BMU_MU with "[-PH] [$]"); [eauto| ]. iIntros "PH".
      iApply OU_BMU.
      iDestruct (OU_create_sig _ _ _ l with "[$]") as "OU".
      iApply (OU_wand with "[-OU]"); [| done].
      iIntros "(%sid & SIG & OBLS)".
      iApply BMU_intro.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
      iSplitR "CP". 
      2: { do 2 iExists _. iFrame. iPureIntro.
           red. reflexivity. }

      iApply wp_value.

      wp_bind (Rec _ _ _). 
      iApply sswp_MU_wp; [done| ].      
      iApply sswp_pure_step; [done| ].
      iNext. iApply (BMU_MU with "[-PH] [$]"); [eauto| ]. iIntros "PH".
      iApply BMU_intro.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
      iSplitR "CP".
      2: { do 2 iExists _. iFrame. iPureIntro.
           red. reflexivity. }
      rewrite union_empty_l_L. 

      iApply wp_value. 

      iApply sswp_MU_wp; [done| ].      
      iApply sswp_pure_step; [done| ].
      iApply (BMU_MU with "[-PH] [$]"); [eauto| ]. iIntros "PH".
      iApply BMU_intro.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
      iSplitR "CP". 
      2: { do 2 iExists _. iFrame. iPureIntro.
           red. reflexivity. }

      simpl. 

      iApply sswp_MUf_wp. iIntros (τ'). iApply (MU__f_wand with "[]").
      2: { iApply (BMU_MU__f with "[-PH]"); [apply LIM_STEPS_LB| ..].
           2: by iFrame.
           iIntros "PH".
           
           iApply OU_BMU.
           iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
           iApply (OU_wand with "[-CP PH]"). 
           2: { iApply (burn_cp_upd with "CP [$]"). }
           iIntros "PH".
           
           iApply BMU_intro. iFrame "PH OBLS".
           iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
           iSplitR "CP".
           2: { do 2 iExists _. iFrame. iPureIntro. reflexivity. }
           iAccu. }

      iIntros "[(POST & CPS' & L & MT & SIG & CPS) R']".
      iDestruct "R'" as (π1 π2) "(PH1 & OB1 & PH3 & OB2 & [%LT1 %LT2])".
      
      iSplitR "POST CPS MT OB1 PH1"; cycle 1.  
      - iApply "POST". 
        iApply (obls_proper with "[$]").
        symmetry. apply subseteq_empty_difference. reflexivity.
      - iApply sswp_MU_wp; [done| ].
        iApply (wp_load with "[$]"). iNext. iIntros.
        iApply (BMU_MU with "[-PH3] [$]"); [eauto| ]. iIntros "PH3".
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
        iApply (obls_proper with "[$]"). set_solver.
    Qed. 

  End TestProg.
    
End ProgramLogic.
