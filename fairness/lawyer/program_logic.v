From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre adequacy.
From trillium.program_logic Require Import ectx_lifting.
From trillium.fairness.heap_lang Require Export heap_lang_defs. 
From trillium.fairness.heap_lang Require Import tactics notation.
From trillium.fairness.lawyer Require Import obligations_model.
From trillium.fairness.heap_lang Require Import sswp_logic.


Close Scope Z. 

Section ProgramLogic.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.
  
  Context `(OP: ObligationsParams Degree Level (locale heap_lang) LIM_STEPS).
  Let OM := ObligationsModel OP.
  
  (* TODO: figure out the proper way *)
  (* Context `{!ObligationsGS OP Σ}.  *)
  (* Context `{EM: ExecutionModel heap_lang OM}. *)
  Let EM := ObligationsEM OP. 

  Context `{hGS: @heapGS Σ _ EM}.


  Section MU.
    (* Context OM *)
    Let oGS : ObligationsGS OP Σ := heap_fairnessGS (heapGS := hGS).
    
    Definition HL_OM_trace_interp' (extr: execution_trace heap_lang)
      (omtr: auxiliary_trace OM) (τ: locale heap_lang): iProp Σ :=
      match extr with
      | {tr[ _ ]} => False
      | extr' :tr[oζ]: c' =>
          let c := trace_last extr' in
          let δ := trace_last omtr in
          gen_heap_interp c'.2.(heap) ∗
          obls_msi OP δ (H1 := oGS) ∗
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
          (* ⌜ k <= LIM_STEPS - n⌝ ∗  *)
          gen_heap_interp c'.2.(heap) ∗
          obls_msi OP δ__k (H1 := oGS) ∗
          ⌜ nsteps (fun p1 p2 => ghost_step OP p1 τ p2) k δ δ__k ⌝ ∗
          ⌜ threads_own_obls OP c δ ⌝ ∗
          ⌜ oζ = Some τ ⌝ ∗
          ⌜ locale_step c (Some τ) c' ⌝
    end.

    
    Definition MU E ζ (P : iProp Σ) : iProp Σ :=
    ∀ extr atr,
      HL_OM_trace_interp' extr atr ζ ={E}=∗
      ∃ δ2 ℓ, state_interp extr (trace_extend atr ℓ δ2) (irisG := @heapG_irisG _ _ _ hGS) ∗ P.

    Lemma burn_cp_upd δ ph deg:
      ⊢ obls_msi OP δ (H1 := oGS) -∗ cp OP ph deg (H1 := oGS) ==∗ obls_msi OP (update_cps OP (ps_cps OP δ ∖ {[+ (ph, deg) +]}) δ) (H1 := oGS).
    Proof.
      iIntros "MSI CP".
      rewrite {1}/obls_msi. iDestruct "MSI" as "(CPS&?&?&?&?&?)".
      destruct δ. simpl. iFrame. simpl.
      rewrite /cp.
      From iris.algebra Require Import gmultiset.
      iCombine "CPS CP" as "?". iApply (own_update with "[$]").
      apply auth_update_dealloc.
      eapply local_update_proper; [..| eapply gmultiset_local_update_dealloc].
      1, 3: reflexivity.
      f_equiv. by rewrite gmultiset_difference_diag.
    Qed.

    (* ⌜ ps_phases OP δ !! τ = Some π__max /\ phase_le ph π__max /\ *)
    Lemma cp_msi_dom δ ph deg:
      ⊢ obls_msi OP δ (H1 := oGS) -∗ cp OP ph deg (H1 := oGS) -∗
        ⌜ (ph, deg) ∈ ps_cps OP δ ⌝.
    Proof.
      rewrite /obls_msi. iIntros "(CPS&_) CP". 
      iCombine "CPS CP" as "CPS". 
      iDestruct (own_valid with "[$]") as %V. iPureIntro.
      apply auth_both_valid_discrete, proj1 in V.
      apply gmultiset_singleton_subseteq_l.
      by apply gmultiset_included.
    Qed. 

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
      ⊢ HL_OM_trace_interp'_step extr omtr τ n -∗ (cp OP ph deg (H1 := oGS)) ==∗
        ∃ δ', state_interp extr (trace_extend omtr τ δ') (irisG := @heapG_irisG _ _ _ hGS).
    Proof.
      iIntros "TI'' cp". rewrite /HL_OM_trace_interp'_step.
      destruct extr; [done| ].
      iDestruct "TI''" as (δ__k) "(HEAP&MSI&%TRANSS&%OBLS&->&%STEP)".
      iDestruct (cp_msi_dom with "[$] [$]") as %CP. 
      iMod (burn_cp_upd with "[$] [$]") as "X".
      iModIntro. iExists _. simpl. iFrame.
      
      pose proof (WIP_th_own_gsteps_ex_phase _ _ _ _ _ _ STEP OBLS TRANSS) as [πτ PHτ]. 

      assert (threads_own_obls OP a (update_cps OP (ps_cps OP δ__k ∖ {[+ (ph, deg) +]}) δ__k)) as TH_OWN'.
      { eapply locale_step_th_obls_pres in OBLS; eauto.
        remember (trace_last extr) as X.
        destruct X as [??], a as [??].
        eapply progress_step_th_obls_pres with (τ := τ); eauto.
        2: { eapply from_locale_step; eauto.
             admit. }
        eexists. split; eauto.
        eexists. split; eauto.
        do 2 eexists. econstructor; eauto.
        apply WIP_all_phases_le. }
      
      iPureIntro. split; auto. 
      
      red. repeat split; auto.
      simpl. red. eexists. split; eauto.
      eexists. split; eauto. do 2 eexists. econstructor; eauto.
      apply WIP_all_phases_le. 
      
    Admitted. 

    (* Definition SMU E ζ n (P : iProp Σ) : iProp Σ := *)
    (* ∀ extr atr, *)
    (*   HL_OM_trace_interp'_step extr atr ζ n ={E}=∗ *)
    (*   ∃ δ2 ℓ, state_interp extr (trace_extend atr ℓ δ2) (irisG := @heapG_irisG _ _ _ hGS) ∗ P. *)

    (* TODO: figure out the correct inequalities *)
    Definition BMU E ζ b (P : iProp Σ) : iProp Σ :=
    ∀ extr atr n,
      (* ⌜ n <= LIM_STEPS - b ⌝ ∗ *)
      HL_OM_trace_interp'_step extr atr ζ n ={E}=∗
      ∃ n', HL_OM_trace_interp'_step extr atr ζ n' ∗ 
            (* ⌜ n <= n' <= LIM_STEPS ⌝ ∗  *)
            ⌜ n' - n <= b ⌝ ∗
            P.

    (* TODO: should we ex quantify ph and deg under BMU? *)
    Lemma BMU_MU E ζ b (P : iProp Σ) ph deg
      (BOUND: b <= LIM_STEPS)
      :
      BMU E ζ b (cp OP ph deg (H1 := oGS) ∗ P) ⊢ MU E ζ P.
    Proof.
      rewrite /MU /BMU. iIntros "BMU" (etr otr) "TI'".
      iSpecialize ("BMU" $! etr otr 0 with "[TI']").
      { rewrite /HL_OM_trace_interp' /HL_OM_trace_interp'_step.
        destruct etr; [done| ].
        iDestruct "TI'" as "(HEAP&MSI&%OBLS&->&%STEP)".
        iExists _. iFrame. iPureIntro.
        repeat split; try done.
        econstructor. }
      iMod "BMU" as (n') "(TI'' & %BOUND' & CP & P)". iFrame.
      iMod (finish_obls_steps with "[$] [$]") as (?) "?".
      { lia. }       
      iModIntro. eauto.
    Qed.

    (* Lemma BMU_step_burn E ζ n P ph deg: *)
    (*    ⊢ BMU E ζ n P -∗ cp OP ph deg (H1 := oGS) -∗ BMU E ζ (S n) P. *)
    (* Proof.  *)

    Definition sgn (sid: SignalId) (l: Level) (b: bool): iProp Σ.
    Admitted. 

    Lemma BMU_step_create_signal E ζ P n l:
       ⊢ (∀ sid, sgn sid l false -∗ BMU E ζ n P) -∗ BMU E ζ (S n) P.
    Proof.
      iIntros "CONT". rewrite /BMU.
    Abort. 
    
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

End ProgramLogic.
