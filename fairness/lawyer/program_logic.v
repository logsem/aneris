From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From trillium.fairness.heap_lang Require Export heap_lang_defs tactics notation sswp_logic.
From trillium.fairness.lawyer Require Import obligations_model.
From trillium.fairness Require Import locales_helpers. 


Close Scope Z. 

    From iris.proofmode Require Import coq_tactics.
    Lemma tac_wp_bind `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM} 
      K Δ s E Φ e f :
      f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
      envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
      envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
    Proof. rewrite envs_entails_unseal=> -> ->. by apply: wp_bind. Qed.

    Ltac wp_bind_core K :=
      lazymatch eval hnf in K with
      | [] => idtac
      | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.
    
    Tactic Notation "wp_bind" open_constr(efoc) :=
      iStartProof;
      lazymatch goal with
      | |- envs_entails _ (wp ?s ?E ?locale ?e ?Q) =>
          first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
                | fail 1 "wp_bind: cannot find" efoc "in" e ]
      | _ => fail "wp_bind: not a 'wp'"
      end.


Section ProgramLogic.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.
  
  Context `(OP: ObligationsParams Degree Level (locale heap_lang) LIM_STEPS).
  Let OM := ObligationsModel OP.
  
  (* TODO: figure out the proper way *)
  (* Context `{!ObligationsGS OP Σ}.  *)
  (* Context `{EM: ExecutionModel heap_lang OM}. *)
  Let EM := ObligationsEM OP. 

  Context `{hGS: @heapGS Σ _ EM}.

  Let oGS : ObligationsGS OP Σ := heap_fairnessGS (heapGS := hGS).

  Section MU.
    
    Definition HL_OM_trace_interp' (extr: execution_trace heap_lang)
      (omtr: auxiliary_trace OM) (τ: locale heap_lang): iProp Σ :=
      match extr with
      | {tr[ _ ]} => False
      | extr' :tr[oζ]: c' =>
          let c := trace_last extr' in
          let δ := trace_last omtr in
          gen_heap_interp c'.2.(heap) ∗
          obls_msi OP δ (H2 := oGS) ∗
          ⌜ threads_own_obls OP c δ ⌝ ∗
          ⌜ oζ = Some τ ⌝ ∗
          ⌜ locale_step c (Some τ) c' ⌝
    end.

    Definition HL_OM_trace_interp'_step (extr: execution_trace heap_lang)
      (omtr: auxiliary_trace OM) (τ: locale heap_lang) (k: nat): iProp Σ :=
      match extr with
      | {tr[ _ ]} => False
      | extr' :tr[oζ]: c' =>
          let c := trace_last extr' in
          let δ := trace_last omtr in
          ∃ δ__k,
          gen_heap_interp c'.2.(heap) ∗
          obls_msi OP δ__k (H2 := oGS) ∗
          ⌜ nsteps (fun p1 p2 => ghost_step OP p1 τ p2) k δ δ__k ⌝ ∗
          ⌜ threads_own_obls OP c δ ⌝ ∗
          ⌜ oζ = Some τ ⌝ ∗
          ⌜ locale_step c (Some τ) c' ⌝
    end.

    
    Definition MU E ζ (P : iProp Σ) : iProp Σ :=
    ∀ extr atr,
      HL_OM_trace_interp' extr atr ζ ={E}=∗
      ∃ δ2 ℓ, state_interp extr (trace_extend atr ℓ δ2) (irisG := @heapG_irisG _ _ _ hGS) ∗ P.

    Lemma sswp_MU_wp_fupd s E E' ζ e Φ
      (NVAL: language.to_val e = None)
      :
      let sswp_post := λ e', (MU E' ζ (|={E',E}=> WP e' @ s; ζ; E {{ Φ }}))%I in
      (|={E,E'}=> sswp s E' e sswp_post)%I -∗
        WP e @ s; ζ; E {{ Φ }}.
    Proof.
      simpl. rewrite wp_unfold /wp_pre.
      iIntros "Hsswp". rewrite NVAL. 
      iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "Hσ".
      iMod "Hsswp" as "foo".
      rewrite /sswp. rewrite NVAL.
      iSimpl in "Hσ". iDestruct "Hσ" as "(%EV & HEAP & MSI)".
      iSpecialize ("foo" with "HEAP").
      iMod "foo" as (Hs) "Hsswp".
      red in Hextr. rewrite Hextr. 
      iModIntro. iSplit.
      { iPureIntro. by rewrite Hextr in Hs. }
      iIntros (e2 σ2 efs Hstep).
      iDestruct ("Hsswp" with "[//]") as "Hsswp".
      iApply (step_fupdN_le 1); [| done| ].
      { pose proof (trace_length_at_least extr). lia. }
      simpl.
      iApply (step_fupd_wand with "Hsswp").
      iIntros ">(Hσ & HMU & ->)".
      rewrite /MU. iSpecialize ("HMU" $! (_ :tr[Some ζ]: _) atr with "[MSI Hσ]").
      { rewrite /HL_OM_trace_interp'.
        rewrite /obls_si. iDestruct "MSI" as "[M %TS]". 
        (* iPoseProof (MSI_tids_smaller with "MSI") as "%TS". *)
        remember (trace_last extr) as xx. destruct xx as [tp h].
        inversion Hextr as [[TP HH]].
        rewrite -TP in TS.
        iApply bi.sep_assoc. iSplitL.
        2: { iPureIntro. repeat split; eauto.
             { replace tp with (tp, h).1 in TS by done.
               rewrite Heqxx in TS. apply TS. }
             simpl in Hζ. 
             rewrite -Hζ. simpl.
             (* rewrite locale_fill'.  *)
             eapply locale_step_atomic.
             3: { eapply @fill_step. apply Hstep. } 
             { rewrite -Heqxx Hextr. simpl. reflexivity. }
             reflexivity. }
        simpl. iFrame. }
      iMod ("HMU") as (??) "[Hσ Hwp]". iMod "Hwp". iModIntro.
      iExists _, _. rewrite right_id_L. by iFrame.
    Qed.

    Lemma MU_wand E ζ (P Q : iProp Σ) :
      (P -∗ Q) -∗ MU E ζ P -∗ MU E ζ Q.
    Proof.
      rewrite /MU. iIntros "HPQ HMU".
      iIntros (extr atr) "Hσ".
      iMod ("HMU" with "Hσ") as (??) "[Hσ HP]". iModIntro.
      iExists _, _. iFrame. by iApply "HPQ".
    Qed.
    
    Lemma sswp_MU_wp s E ζ e (Φ : val → iProp Σ)
      (NVAL: language.to_val e = None):
      sswp s E e (λ e', MU E ζ (WP e' @ s; ζ;  E {{ Φ }})) (hGS := hGS) -∗
        WP e @ s; ζ; E {{ Φ }}.
    Proof.
      iIntros "Hsswp". iApply sswp_MU_wp_fupd; auto. iModIntro.
      iApply (sswp_wand with "[] Hsswp").
      iIntros (?) "HMU". iApply (MU_wand with "[] HMU"). by iIntros "$ !>".
    Qed.
    
  End MU.

  Section BMU.

    Definition BMU E ζ b (P : iProp Σ) : iProp Σ :=
    ∀ extr atr n,
      (* ⌜ n <= LIM_STEPS - b ⌝ ∗ *)
      HL_OM_trace_interp'_step extr atr ζ n ={E}=∗
      ∃ n', HL_OM_trace_interp'_step extr atr ζ n' ∗ 
            (* ⌜ n <= n' <= LIM_STEPS ⌝ ∗  *)
            ⌜ n' - n <= b ⌝ ∗
            P.

    (* TODO: clarify how to derive this fact *)
    Lemma WIP_th_own_ex_phase c τ c' δ
      (STEP: locale_step c (Some τ) c')
      (OBLS: threads_own_obls OP c δ):
      exists π, ps_phases OP δ !! τ = Some π.
    Proof. Admitted.

    (* TODO: ghost steps should preserve it *)
    Lemma WIP_th_own_gsteps_ex_phase c τ c' δ δ' n
      (STEP: locale_step c (Some τ) c')
      (OBLS: threads_own_obls OP c δ)
      (GSTEPS: relations.nsteps (fun p1 p2 => ghost_step OP p1 τ p2) n δ δ'):
      exists π, ps_phases OP δ' !! τ = Some π.
    Proof. Admitted.

    Lemma WIP_all_phases_le π1 π2:
      phase_le π1 π2.
    Proof. done. Qed.

    Lemma finish_obls_steps extr omtr τ n ph deg
      (BOUND: n <= LIM_STEPS)
      :
      ⊢ HL_OM_trace_interp'_step extr omtr τ n -∗ (cp OP ph deg (H2 := oGS)) ==∗
        ∃ δ', state_interp extr (trace_extend omtr τ δ') (irisG := @heapG_irisG _ _ _ hGS).
    Proof.
      iIntros "TI'' cp". rewrite /HL_OM_trace_interp'_step.
      destruct extr; [done| ].
      iDestruct "TI''" as (δ__k) "(HEAP&MSI&%TRANSS&%OBLS&->&%STEP)".
      iDestruct (cp_msi_dom with "[$] [$]") as %CP. 

      pose proof (WIP_th_own_gsteps_ex_phase _ _ _ _ _ _ STEP OBLS TRANSS) as [πτ PHτ]. 
      iMod (burn_cp_upd_impl with "[$] [$]") as "X".
      { eexists. split; eauto. apply WIP_all_phases_le. }
      iDestruct "X" as "(%δ' & MSI & %BURNS)". 
      iModIntro. iExists _. simpl. iFrame.
      
      assert (threads_own_obls OP a δ') as TH_OWN'.
      { eapply locale_step_th_obls_pres in OBLS; eauto.
        remember (trace_last extr) as X.
        destruct X as [??], a as [??].
        eapply progress_step_th_obls_pres with (τ := τ); eauto.
        2: { eapply from_locale_step; eauto.
             replace l with ((l, s).1) by auto. 
             eapply locale_step_from_locale_src; eauto. }
        eexists. split; eauto.
        eexists. split; eauto. }
      
      iPureIntro. split; auto.      
      red. repeat split; auto.
      simpl. red. eexists. split; eauto.
      eexists. split; eauto.      
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

    Lemma BMU_MU E ζ b (P : iProp Σ)
      (BOUND: b <= LIM_STEPS)
      :
      (BMU E ζ b (P ∗ ∃ ph deg, cp OP ph deg (H2 := oGS))) ⊢ MU E ζ P.
    Proof.
      rewrite /MU /BMU. iIntros "BMU" (etr otr) "TI'".
      iSpecialize ("BMU" $! etr otr 0 with "[TI']").
      { rewrite /HL_OM_trace_interp' /HL_OM_trace_interp'_step.
        destruct etr; [done| ].
        iDestruct "TI'" as "(HEAP&MSI&%OBLS&->&%STEP)".
        iExists _. iFrame. iPureIntro.
        repeat split; try done.
        econstructor. }
      iMod "BMU" as (n') "(TI'' & %BOUND' & P & (%ph & %deg & CP))". iFrame. 
      iMod (finish_obls_steps with "[$] [$]") as (?) "?".
      { lia. }       
      iModIntro. eauto.
    Qed.

    Lemma OU_BMU_hmmm E ζ P b:
       ⊢ (P -∗ BMU E ζ b P) -∗ OU OP ζ P (H2 := oGS) -∗ BMU E ζ (S b) P.
    Proof.
      iIntros "CONT OU". rewrite {2}/BMU /HL_OM_trace_interp'_step.
      iIntros (etr atr n) "TI'". destruct etr; [done| ].
      iDestruct "TI'" as "(%δ & HEAP & MSI & %TRANS1 & %TH_OWN & -> & %STEP)".
      rewrite /OU. iMod ("OU" with "[$]") as "(%δ' & MSI & %TRANS2 & P)".
      iSpecialize ("CONT" with "[$]"). rewrite /BMU.
      iSpecialize ("CONT" $! (etr :tr[ _ ]: _) with "[HEAP MSI]").
      { rewrite /HL_OM_trace_interp'_step. iExists _.  iFrame.
        iPureIntro. repeat split; eauto.
        eapply rel_compose_nsteps_next. eexists. split; eauto. }
      iMod "CONT" as "(%n' & TI' & %BOUND' & P)". iModIntro.
      iExists _. iFrame. iPureIntro. lia. 
    Qed.

    Lemma OU_BMU E ζ P b:
       ⊢ OU OP ζ (BMU E ζ b P) (H2 := oGS) -∗ BMU E ζ (S b) P.
    Proof.
      iIntros "OU". rewrite {2}/BMU /HL_OM_trace_interp'_step.
      iIntros (etr atr n) "TI'". destruct etr; [done| ].
      iDestruct "TI'" as "(%δ & HEAP & MSI & %TRANS1 & %TH_OWN & -> & %STEP)".
      rewrite /OU. iMod ("OU" with "[$]") as "(%δ' & MSI & %TRANS2 & CONT)".
      iSpecialize ("CONT" $! (etr :tr[ _ ]: _) with "[HEAP MSI]").
      { rewrite /HL_OM_trace_interp'_step. iExists _.  iFrame.
        iPureIntro. repeat split; eauto.
        eapply rel_compose_nsteps_next. eexists. split; eauto. }
      iMod "CONT" as "(%n' & TI' & %BOUND' & P)". iModIntro.
      iExists _. iFrame. iPureIntro. lia. 
    Qed.

    (* an example usage of OU *)
    Lemma BMU_step_create_signal E ζ P b l R:
       ⊢ (∀ sid, sgn OP sid l (Some false) (H2 := oGS) -∗ obls OP ζ (R ∪ {[ sid ]}) (H2 := oGS) -∗ BMU E ζ b P) -∗ obls OP ζ R (H2 := oGS) -∗ BMU E ζ (S b) P.
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
          !"x"
    .

    Hypothesis (LIM_STEPS_LB: 5 <= LIM_STEPS). 

    Lemma test_spec (τ: locale heap_lang) (π: Phase) (d: Degree) (l: Level):
      {{{ cp_mul OP π d 10 (H2 := oGS) ∗ th_phase_ge OP τ π (H2 := oGS) ∗ obls OP τ ∅ (H2 := oGS)}}}
        test_prog @ τ
      {{{ x, RET #x; obls OP τ ∅ (H2 := oGS) }}}.
    Proof.
      iIntros (Φ). iIntros "(CPS & #PH & OBLS) POST".
      rewrite /test_prog. 

      wp_bind (_ + _)%E.
      iApply sswp_MU_wp; [done| ].
      iApply sswp_pure_step; [done| ].
      rewrite /Z.add. simpl. 
      iApply BMU_MU; [reflexivity| ].
      iNext. iApply BMU_intro.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
      iSplitR "CP"; [| by eauto].

      iApply wp_value.

      wp_bind (ref _)%E. 
      iApply sswp_MU_wp; [done| ].
      iApply wp_alloc. iIntros "!> %x L ?".
      iApply BMU_MU; eauto.
      iApply OU_BMU.
      iDestruct (OU_create_sig _ _ _ l with "[$]") as "OU".
      Unshelve. 2: apply _. 
      iApply (OU_wand with "[-OU]"); [| done].
      iIntros "(%sid & SIG & OBLS)".
      iApply BMU_intro.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
      iSplitR "CP"; [| by eauto].

      iApply wp_value.
      (* Set Printing All. *)
      (* Unset Printing Notations. *)

      wp_bind (Rec _ _ _). 
      iApply sswp_MU_wp; [done| ].      
      iApply sswp_pure_step; [done| ].
      iApply BMU_MU; [eauto| ].
      iNext.
      iApply OU_BMU.
      iDestruct (OU_set_sig with "OBLS SIG") as "OU"; [set_solver| ].
      iApply (OU_wand with "[-OU]"); [| done].
      iIntros "(SIG & OBLS)".
      iApply BMU_intro.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
      iSplitR "CP"; [| by eauto].

      iApply wp_value. 

      iApply sswp_MU_wp; [done| ].      
      iApply sswp_pure_step; [done| ].
      iApply BMU_MU; [reflexivity| ].
      iNext. iApply BMU_intro.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
      iSplitR "CP"; [| by eauto].

      simpl. 
      iApply sswp_MU_wp; [done| ].
      iApply (wp_load with "[$]"). iNext. iIntros.
      iApply BMU_MU; [reflexivity| ].
      iApply BMU_intro.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
      iSplitR "CP"; [| by eauto].

      iApply wp_value. 
      iApply "POST".
      rewrite difference_union_distr_l_L difference_diag_L subseteq_empty_difference_L; [| done].
      by rewrite union_empty_r_L. 
    Qed.

  End TestProg.
    
End ProgramLogic.
