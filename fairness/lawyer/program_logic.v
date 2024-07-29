From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre adequacy.
From trillium.program_logic Require Import ectx_lifting.
From trillium.fairness.heap_lang Require Export heap_lang_defs. 
From trillium.fairness.heap_lang Require Import tactics notation.
From trillium.fairness.lawyer Require Import obligations_model.
From trillium.fairness.heap_lang Require Import sswp_logic.


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

    Definition MU E ζ (P : iProp Σ) : iProp Σ :=
    ∀ extr atr,
      HL_OM_trace_interp' extr atr ζ ={E}=∗
      ∃ δ2 ℓ, state_interp extr (trace_extend atr ℓ δ2) (irisG := @heapG_irisG _ _ _ hGS) ∗ P.

    Lemma sswp_MU_wp_fupd s E E' ζ e Φ
      (NVAL: language.to_val e = None)
      :
      let sswp_post := λ e', (MU E' ζ ((|={E',E}=> WP e' @ s; ζ; E {{ Φ }})))%I in
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
