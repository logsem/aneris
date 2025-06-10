From iris.proofmode Require Import tactics coq_tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import locales_helpers utils. 
From lawyer.obligations Require Import obligations_model obls_utils obligations_resources obligations_am obligations_em obligations_wf.
From lawyer Require Import sub_action_em program_logic action_model.
From heap_lang Require Export heap_lang_defs tactics notation sswp_logic locales_helpers_hl.


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

    Lemma BOU_AMU__f E ζ ζ' π R0 R' P:
      ⊢
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

    (* TODO: make this version the main one *)
    Lemma BOU_AMU__f' E ζ ζ' π R0 R' P:
      ⊢
        let om_fork_post := ∃ π1 π2,
            th_phase_eq ζ π1 ∗ obls ζ (R0 ∖ R') ∗ 
            th_phase_eq ζ' π2 ∗ obls ζ' (R0 ∩ R') ∗
            ⌜ phase_lt π π1 /\ phase_lt π π2 ⌝ in
        BOU E LIM_STEPS ((om_fork_post -∗ P) ∗ ∃ d, cp π d ∗ obls ζ R0 ∗ th_phase_eq ζ π) -∗
        AMU__f E ζ ζ' obls_act P (aeGS := oGS').
    Proof using.
      simpl. iIntros "BOU".
      iApply AMU_impl_wand.
      2: { iApply (BOU_AMU__f with "[$]"). }
      iIntros "[X Y]".
      by iApply "X".
    Qed.      

  End BOU.

  Global Instance ElimOU p P Q:
    ElimModal True p false (OU P) P (OU Q) Q.
  Proof using.
    red. simpl. iIntros "_ [OP PQ]".
    iApply (OU_wand with "[$]").
    by iApply bi.intuitionistically_if_elim.
  Qed.

  Global Instance ElimOU_BOU p P Q E n:
    ElimModal (0 < n) p false (OU P) P (BOU E n Q) (BOU E (n - 1) Q).
  Proof using.
    red. simpl. iIntros "%NZ [OP PQ]".
    apply Nat.le_sum in NZ as [? ->]. rewrite Nat.sub_add'. 
    iApply OU_BOU. 
    iDestruct (bi.intuitionistically_if_elim with "OP") as "OP".
    iMod "OP". by iApply "PQ".
  Qed.
  (* Global Instance ElimOU_BOU p P Q E n m: *)
  (*   S m <= n -> ElimModal True p false (OU P) P (BOU E n Q) (BOU E (n - 1) Q). *)
  (* Proof using. *)
  (*   clear LIM_STEPS_LB.  *)
  (*   intros. red. simpl. iIntros "%NZ [OP PQ]". *)
  (*   iApply OU_BOU'; [lia| ]. *)
  (*   iDestruct (bi.intuitionistically_if_elim with "OP") as "OP". *)
  (*   iMod "OP". by iApply "PQ". *)
  (* Qed. *)

  Global Instance ElimModal_BOU_split p E k n P Q:
    ElimModal (k <= n) p false
              (BOU E k P) P
              (BOU E n Q) (BOU E (n - k) Q).
  Proof using.
    red. iIntros "%LE (BOU & IMPL)".
    iDestruct (bi.intuitionistically_if_elim with "BOU") as "BOU".
    apply Nat.le_sum in LE as [? ->]. rewrite Nat.sub_add'.
    iApply BOU_split. iApply (BOU_wand with "[$] [$]").
  Qed.

  Global Instance FromModal_BOU E n P:
    FromModal True modality_id (BOU E n P) (BOU E n P) P.
  Proof using.
    red. simpl. iIntros "_". iApply BOU_intro.
  Qed.

  Global Instance ElimModal_bupd_BOU p E n P Q:
    ElimModal True p false
    (|==> P) P
    (BOU E n Q) (BOU E n Q).
  Proof using.
    clear. 
    red. simpl. iIntros "_ [P IMPL]".
    rewrite bi.intuitionistically_if_elim.
    iMod "P". by iApply "IMPL". 
  Qed.

  Global Instance ElimModal_fupd_BOU p E' E n P Q:
    ElimModal (E' ⊆ E) p false
    (|={E'}=> P) P
    (BOU E n Q) (BOU E n Q).
  Proof using.
    clear. 
    red. simpl. iIntros "%SUB [P IMPL]".
    rewrite bi.intuitionistically_if_elim. 
    iApply BOU_invs.
    iMod (fupd_mask_subseteq E') as "CLOS"; [done| ]. iMod "P".
    iApply (BOU_mask_comm with "[$]").
    { set_solver. }
    iFrame. iMod "CLOS".  
    iApply fupd_mask_intro_subseteq; [set_solver | done].
  Qed.

  Global Instance frame_BOU p E n R P Q:
    (Frame p R P Q) →
    Frame p R (BOU E n P) (BOU E n Q).
  Proof using.
    red. intros FRAME. iIntros "[R BOU]".
    red in FRAME.
    iMod "BOU" as "?". iModIntro.
    iApply FRAME. iFrame.
  Qed.

  Global Instance FromExist_BOU {A: Type} E n P (Φ: A -> iProp Σ):
    FromExist P Φ ->
    FromExist (BOU E n P) (fun x => BOU E n (Φ x)).
  Proof using.
    rewrite /FromExist. iIntros (EX) "[%x BOU]".
    iMod "BOU". iModIntro.
    iApply EX. by iExists _.
  Qed.

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
    iApply wp_alloc. iIntros "!> %x L _".
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

    replace 6 with (4 + 2). iDestruct (cp_mul_split with "CPS") as "[CPS CP]". 
    iApply sswp_MUf_wp. iIntros (τ'). iApply (MU__f_wand with "[CPS CPS' L SIG POST]").
    2: {
      iApply OBLS_AMU__f; [by rewrite nclose_nroot| ]. 
      iApply BOU_AMU__f.
      iNext. 
      iDestruct (cp_mul_take with "CP") as "[CPS CP]".
      iMod (burn_cp_upd with "CP [$]") as "PH"; [lia| ].
      iModIntro. iFrame "PH OBLS".
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
      iSplitR "CP".
      2: { iExists _. iFrame. }
      iAccu.
    }

    (* iIntros "[(POST & CPS' & L & SIG & CPS) R']". *)
    iIntros "[_ R']".
    iDestruct "R'" as (π1 π2) "(PH1 & OB1 & PH3 & OB2 & [%LT1 %LT2])".

    iSplitR "POST CPS OB1 PH1"; cycle 1.  
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
    - lia.
  Qed.

End TestProg.
