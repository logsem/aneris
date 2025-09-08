From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From fairness Require Import fairness locales_helpers.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination obligations_wf.
From lawyer.nonblocking Require Import trace_context wptp_gen.
From trillium.program_logic Require Import execution_model weakestpre adequacy_utils adequacy_cond simulation_adequacy_em_cond. 
From lawyer Require Import action_model sub_action_em.
From lawyer Require Import program_logic.  
From heap_lang Require Import sswp_logic. 


Section Pwp.

  Definition LoopingModel: Model :=
    {| mstate := unit; mlabel := unit; mtrans := fun _ _ _ => True |}.

  (* Definition pwp {Λ: language} {Σ: gFunctors} := @wp Λ (iProp Σ) LoopingModel. *)
  (* Definition pwp := @wp (A := LoopingModel). *)
  (* Definition pwp {Λ: language} {PROP} := @wp Λ PROP LoopingModel. *)
  (* Global Arguments pwp {_ _ _}.  wp *)
  Definition pwp `{!irisG Λ LoopingModel Σ} :=
    @wp Λ (iProp Σ) stuckness _. 

End Pwp. 


Definition phys_SI {Λ} (LG: LangEM Λ) `{invGS_gen HasNoLc Σ} {lG: lgem_GS Σ}
  (etr: execution_trace Λ) (_: auxiliary_trace LoopingModel): iProp Σ :=
  lgem_si (trace_last etr).2 (lgem_GS0 := lG).

(** not turning these into instances to avoid incorrect Iris instantiations *)

Definition irisG_looping {Λ} (LG: LangEM Λ) `{invGS_gen HasNoLc Σ} {lG: lgem_GS Σ}:
  irisG Λ LoopingModel Σ := {|
    state_interp := phys_SI LG (lG := lG);
    fork_post := fun _ _ => (⌜ True ⌝)%I;
|}. 

(* TODO: rename *)
Definition iris_OM_into_Looping {Σ} `(Hinv : @IEMGS Λ M LG EM Σ):
  irisG Λ LoopingModel Σ.
Proof using.
  eapply irisG_looping; apply Hinv.  
Defined.


Definition looping_trace: auxiliary_trace LoopingModel :=
  trace_singleton ().


Lemma pwp_MU_ctx_take_step {Σ} `{Hinv : @IEMGS heap_lang M HeapLangEM EM Σ}
    s Φ ex atr tp1 K e1 tp2 σ1 e2 σ2 efs ζ P:
    let (E1, E2) := (ectx_fill K e1, ectx_fill K e2) in
    valid_exec ex →
    prim_step e1 σ1 e2 σ2 efs ->
    trace_ends_in ex (tp1 ++ E1 :: tp2, σ1) →
    locale_of tp1 E1 = ζ ->
    state_interp ex atr -∗
    (let hGS: @heapGS Σ M EM := {| heap_iemgs := Hinv |} in
     let oτ' := step_fork (trace_last ex) (tp1 ++ E2 :: tp2 ++ efs, σ2) in
     @MU_impl _ EM Σ hGS oτ' ⊤ ζ P ) -∗
    (let _ := iris_OM_into_Looping in pwp s ⊤ ζ e1 Φ)
    ={⊤,∅}=∗   |={∅}▷=>^(S $ trace_length ex)   |={∅,⊤}=>
    ∃ δ' ℓ,
      state_interp (trace_extend ex (Some ζ) (tp1 ++ E2 :: tp2 ++ efs, σ2))
                   (trace_extend atr ℓ δ') ∗
      (let _ := iris_OM_into_Looping in pwp s ⊤ ζ e2 Φ) ∗ 
      ([∗ list] i↦ef ∈ efs,
        let τf := locale_of (tp1 ++ E1 :: tp2 ++ take i efs) ef in
        (let _ := iris_OM_into_Looping in pwp s ⊤ τf ef
                                            (fork_post τf) (* for pwp *)
                                            (* (let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in *)
                                            (*   fun _ => obls τf ∅) *)
        )
      ) ∗
      P.
Proof using.
  simpl.
  iIntros (Hex Hstp Hei Hlocale) "HSI MU Hwp".
  rewrite /pwp. 
  rewrite wp_unfold /wp_pre.
  destruct (to_val e1) eqn:He1.
  { erewrite val_stuck in He1; done. }
  simpl. 
  iDestruct "HSI" as "(%EV & PHYS & MSI)". simpl. 
  iMod ("Hwp" $! _ looping_trace K with "[//] [] [] PHYS") as "[Hs Hwp]".
  1, 2: done.
  iDestruct ("Hwp" with "[]") as "Hwp"; first done.
  iModIntro. 
  iApply (step_fupdN_wand with "Hwp").
  iIntros "!> Hwp".
  iMod "Hwp" as ([] []) "(PHYS & WP & WPS')".
  
  rewrite /MU /MU_impl. iMod ("MU" $! (trace_extend _ _ (_, _)) with "[PHYS MSI]") as (δ ρ) "TI".
  { rewrite /trace_interp_interim.
    iFrame.
    iPureIntro. split.
    { rewrite -Hlocale. reflexivity. }
    split; [| done]. 
    rewrite -Hlocale. econstructor; eauto.
    simpl in Hstp. simpl.
    by apply fill_prim_step. }
  
  iModIntro.
  simpl.  iDestruct "TI" as "((%&?&?)&?)". 
  do 2 iExists _. subst ζ. iFrame. 
  iPureIntro. congruence. 
Qed.


(* TODO: move? try to unify with sswp_MU_wp_fupd  *)
Lemma sswp_pwp {Σ} {iG: invGS_gen HasNoLc Σ} {hG: heap1GS Σ}
  s E E' τ e Φ
  (NVAL: language.to_val e = None):
  let iG := irisG_looping HeapLangEM (lG := hG) in 
  (|={E,E'}=> sswp s E' e (λ e', ▷ |={E',E}=> pwp s E τ e' Φ)%I) -∗
    pwp s E τ e Φ.
Proof using.
  rewrite /pwp wp_unfold /wp_pre.
  iIntros "Hsswp". rewrite NVAL. 
  iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "Hσ".
  iMod "Hsswp" as "foo".
  rewrite /sswp. rewrite NVAL.
  iSimpl in "Hσ".
  iSpecialize ("foo" with "[$]").
  iMod "foo" as (Hs) "Hsswp".
  red in Hextr. rewrite Hextr. 
  iModIntro. iSplit.
  { iPureIntro. by rewrite Hextr in Hs. }
  iIntros (e2 σ2 efs Hstep).
  iDestruct ("Hsswp" with "[//]") as "Hsswp".
  iApply (step_fupdN_le 2); [| done| ].
  { pose proof (trace_length_at_least extr). lia. }
  simpl.
  iApply (step_fupd_wand with "Hsswp").
  iIntros ">(Hσ & HMU & ->)".
  iApply fupd_mask_intro; [set_solver| ]. iIntros "CLOS' !> !>".
  iMod "CLOS'" as "_". iMod "HMU". iModIntro.
  iExists tt, tt. by iFrame.
Qed. 
