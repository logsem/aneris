From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap.
From trillium.fairness.heap_lang Require Import tactics notation sswp_logic.
From trillium.fairness Require Import fairness resources fuel model_plug lm_fair.
From trillium.fairness.lm_rules Require Import model_step resources_updates fuel_step.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From trillium.program_logic Require Import ewp.

Section LMLocalRules.
  
  (* Context {M: FairModel}. *)
  (* Context {msi: fmstate M -> iProp Σ}.  *)
  (* Context {lifted_roles: fmstate M -> gset (fmrole M)}. *)
  
  Context `{Countable G}.
  Context `{iLM: LiveModel G iM LSI}.
  Context {LFP: LMFairPre iLM}.
  Let LF := LM_Fair (LF := LFP).
  Context `{fGS: @fairnessGS _ _ _ _ _ iLM Σ}. 
  Let msi: fmstate LF -> iProp Σ := model_state_interp (LM := iLM).

  Context {lifted_roles: fmstate LF -> gset (fmrole LF)}.
  Hypothesis (IMPL_LIFT: forall (δ1 δ2: fmstate LF) g R2,
                 (* dom (ls_tmap δ') = dom (ls_tmap δ) -> *)
                 (* live_roles _ δ' ⊆ live_roles _ δ -> *)
                 locale_trans δ1 g δ2 (LM := iLM) ->
                 ls_tmap δ2 = <[g:=R2]> (ls_tmap δ1) ->
                 lifted_roles δ2 ⊆ lifted_roles δ1).
  (* Hypothesis (TRANS_NO_ENAB: forall δ g δ', *)
  (*                locale_trans δ g δ' (LM := iLM) -> *)
  (*                live_roles LF δ' ⊆ live_roles LF δ).  *)
  
  Let lm_local_rule := local_rule (msi := msi) (lifted_roles := lifted_roles). 
  
  Lemma model_step_local_rule s1 s2 fs1 fs2 ρ ζ fr1 fr_stash:
    ⊢ lm_local_rule
      (⌜ live_roles _ s2 ∖ live_roles _ s1 ⊆ fr1 ∪ dom fs1 ∩ dom fs2 ⌝ ∗
       ⌜ fr_stash ⊆ dom fs1 ⌝ ∗
       ⌜ live_roles _ s1 ∩ (fr_stash ∖ {[ ρ ]}) = ∅ ⌝ ∗
       ⌜ dom fs2 ∩ fr_stash = ∅ ⌝ ∗
       ⌜ fmtrans _ s1 (Some ρ) s2 ⌝ ∗
       ⌜ valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := iLM) ⌝ ∗
       ⌜ model_step_preserves_LSI s1 ρ s2 fs1 fs2 (LSI := LSI) ⌝ ∗
       has_fuels ζ fs1 ∗ 
       frag_model_is s1 ∗
       frag_free_roles_are fr1)
      ( has_fuels ζ fs2 ∗ 
        frag_model_is s2 ∗ 
        frag_free_roles_are (fr1 ∖ (live_roles _ s2 ∖ (live_roles _ s1 ∪ dom fs1 ∩ dom fs2)) ∪ fr_stash))
      ζ.
  Proof. 
    rewrite /lm_local_rule /local_rule. iModIntro.
    iIntros (?) "((%&%&%&%&%&%&%&?&?&?)&?)".
    iMod (actual_update_step_still_alive_gen with "[$][$][$][$]") as "NEW"; eauto.
    iDestruct "NEW" as (?) "(%STEP&?&?&?&?&%TM)".
    iModIntro. iExists _. iFrame.
    iPureIntro.
    assert (fmtrans LF δ (Some ζ) δ2) as STEP'. 
    { simpl. eexists. split; [apply STEP| ]. done. }
    split; [done| ].
    eapply IMPL_LIFT; eauto.
    apply STEP'. 
  Qed.

  Lemma fuel_keep_step_local_rule fs ζ:
    ⊢ lm_local_rule
      (⌜ dom fs ≠ ∅ ⌝ ∗
       ⌜ LSI_fuel_independent (LSI := LSI) ⌝ ∗
       has_fuels_S ζ fs)
      (has_fuels ζ fs)
      ζ.
  Proof.
    rewrite /lm_local_rule /local_rule. iModIntro.
    iIntros (?) "((%&%&?)&?)".
    iMod (actual_update_no_step_enough_fuel_keep with "[$][$]") as "NEW"; eauto.
    iDestruct "NEW" as (?) "(%STEP&?&?&%TM)".
    iExists _. iFrame. 
    iPureIntro.
    assert (fmtrans LF δ (Some ζ) δ2) as STEP'. 
    { simpl. eexists. split; [apply STEP| ]. done. }
    split; [done| ].
    pose proof STEP' as [foo bar]%locale_trans_dom%elem_of_dom. 
    eapply IMPL_LIFT; eauto.
    { apply STEP'. }
    rewrite TM. symmetry.
    by apply insert_id.
  Qed.

  Lemma fuel_drop_step_local_rule rem s fs ζ:
    ⊢ lm_local_rule
    (⌜ dom fs ≠ ∅ ⌝ ∗
     ⌜ (live_roles _ s) ∩ rem = ∅ ⌝ ∗
     ⌜ rem ⊆ dom fs ⌝ ∗
     ⌜ fuel_drop_preserves_LSI s rem (LSI := LSI) ⌝ ∗
     has_fuels_S ζ fs ∗
     partial_model_is s)
    (has_fuels ζ (fs ⇂ (dom fs ∖ rem)) ∗
     partial_model_is s)
    ζ.
  Proof. 
    rewrite /lm_local_rule /local_rule. iModIntro.
    iIntros (?) "((%&%&%&%&?&?)&?)".
    iMod (actual_update_no_step_enough_fuel_drop with "[$][$][$]") as "NEW"; eauto.
    iDestruct "NEW" as (?) "(%STEP&?&?&?&%TM)".
    iExists _. iFrame. 
    iPureIntro.
    assert (fmtrans LF δ (Some ζ) δ2) as STEP'. 
    { simpl. eexists. split; [apply STEP| ]. done. }
    split; [done| ].
    eapply IMPL_LIFT; eauto.
    apply STEP'. 
  Qed. 

End LMLocalRules.  




Section ModelLogic.
  Context `{EM: ExecutionModel heap_lang M__glob}.
  Context `{hGS: @heapGS Σ _ EM}.
  (* Let eGS := heap_fairnessGS. *)

  Context {M: FairModel}.
  Context {msi: fmstate M -> iProp Σ}.
  Context {lifted_roles: fmstate M -> gset (fmrole M)}.
  Let step_restr st1 st2 := lifted_roles st2 ⊆ lifted_roles st1. 

  (* TODO: figure out the proper way *) 
  Let PI (p: state heap_lang) := gen_heap_interp p.(heap). 

  Let ewp'_instance_helper := ewp' (PI := PI) (MSI := msi) (step_restr := step_restr).  
  Existing Instance ewp'_instance_helper. 

  (* Let CWP := @cwp _ _ EM _ eGS _ msi lifted_roles _. *)
  Let lmu := @LMU _ _ msi lifted_roles. 

  (* TODO: move *)
  Lemma wand_proper (P1 Q1 P2 Q2: iProp Σ):
    (P1 -∗ P2) -∗ (Q1 -∗ Q2) -∗ (P1 ∗ Q1 -∗ P2 ∗ Q2).
  Proof.
    iIntros "PP QQ [P Q]". iSplitL "PP P".
    - iApply ("PP" with "P"). 
    - iApply ("QQ" with "Q").
  Qed. 

  Lemma sswp_MU_wp_fupd s tid E ε__lift E' e Φ
    (SUB': ε__lift ⊆ E'):
    (|={E, E'}=> sswp s ε__lift e 
                 (λ e', MU ε__lift tid ((|={E',E}=> WP e' @ s; tid; E {{ Φ }})) (eGS := heap_fairnessGS)))%I -∗
      WP e @ s; tid; E {{ Φ }}. 
  Proof.
    rewrite wp_unfold /wp_pre.
    iIntros "Hsswp".
    destruct (to_val e) eqn:Heqn.
    { rewrite /sswp Heqn. 
      iMod "Hsswp" as "?". iExFalso. done. }
    iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "Hσ".
    iMod "Hsswp" as "Hsswp".
    simpl.
    iDestruct "Hσ" as "(%EV & HI & MSI)". 
    rewrite /sswp Heqn.
    iApply fupd_mask_weaken; [apply SUB'| ]. iIntros "CLOS'".  
    iMod ("Hsswp" with "HI") as (Hs) "Hsswp".
    simpl in Hextr. red in Hextr. rewrite Hextr in Hs. rewrite Hextr.  
    iModIntro. iSplit; [done| ]. 
    iIntros (e2 σ2 efs Hstep).
    iMod ("Hsswp" with "[//]") as "Hsswp".
    iModIntro. iNext. iMod "Hsswp". iModIntro.

    iApply step_fupdN_intro; [done| ].      
    
    iNext. 
    iMod "Hsswp" as "(Hσ & HMU & ->)". iFrame. 

    iMod ("HMU" with "MSI []") as (??) "(Hσ & %EV' & Hwp)".
    { iPureIntro. rewrite -Hζ. 
      econstructor; eauto. rewrite Hζ.
      eapply fill_prim_step; eauto. }
    iMod "CLOS'" as "_". 
    iMod "Hwp". iModIntro.
    iExists _, _. simpl in *. rewrite right_id_L. simpl. iFrame.
    iPureIntro. simpl in *. rewrite right_id_L in EV'. done. 
  Qed.

  Notation "'EWP' e @ s ; ρ ; E {{ Φ } }" := (ewp s E ρ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

  Lemma sswp_MU_ewp_fupd s ρ E E' e Φ:
    (|={E, E'}=> sswp s E' e 
                 (λ e', lmu ρ (|={E',E}=> EWP e' @ s; ρ; E {{ Φ }})))%I -∗
      EWP e @ s; ρ; E {{ Φ }}.
  Proof.
    (* rewrite /CWP /cwp. *)
    iIntros "Hsswp".

    rewrite ewp_unfold /ewp_pre.
    destruct (to_val e) eqn:Heqn.
    { rewrite /sswp Heqn. 
      iMod "Hsswp" as "?". iExFalso. done. }
    iIntros (σ1 δ1) "PI MSI".
    iMod "Hsswp" as "Hsswp".
    rewrite /sswp Heqn.
    rewrite /PI.
    iMod ("Hsswp" with "PI") as "[%RED STEP]". 
    iModIntro. iSplit; [done| ].
    iIntros (e2 σ2 efs Hstep).
    iSpecialize ("STEP" with "[//]").
    iMod "STEP". iModIntro. iNext. iMod "STEP". iModIntro. iMod "STEP".
    iDestruct "STEP" as "(PI & LMU & ->)".
    rewrite /lmu /LMU. iMod ("LMU" with "MSI") as (?) "(EWP & MSI & %TRANS & %LR)".
    iMod "EWP". iModIntro. iExists _. iFrame. done.
  Qed. 

  Lemma sswp_MU_ewp s ρ E e Φ:
    (sswp s E e 
                 (λ e', lmu ρ (EWP e' @ s; ρ; E {{ Φ }})))%I -∗
      EWP e @ s; ρ; E {{ Φ }}.
  Proof.
    iIntros "Hsswp".
    iApply sswp_MU_ewp_fupd. iModIntro.     
    iApply (sswp_wand with "[-Hsswp]"); [| by iFrame].
    iIntros. iApply LMU_mono; [| by iFrame]. intuition.
  Qed.       

Section Tactics.

  Lemma tac_ewp_bind
    K Δ (e: expr heap_lang) (Φ: val heap_lang -> iProp Σ) (s: stuckness) E (ρ: fmrole M) f:
    f = (λ e, fill K e) ->
        envs_entails Δ (ewp s E ρ e%E (fun v => ewp s E ρ (f (Val v)) Φ)) ->
        envs_entails Δ (ewp s E ρ (fill K e) Φ).
  Proof. rewrite envs_entails_unseal=> -> ->. by apply: ewp_bind. Qed.

End Tactics.

End ModelLogic.

  Ltac ewp_bind_core K :=
    lazymatch eval hnf in K with
    | [] => idtac
    | _ => eapply (tac_ewp_bind K); [simpl; reflexivity|reduction.pm_prettify]
    end.

  Tactic Notation "ewp_bind" open_constr(efoc) :=
    iStartProof;
    lazymatch goal with
    | |- envs_entails _
          (* (wp ?s ?E ?locale ?e ?Q) *)
          (* (cwp ?e ?Φ ?s ?ε__wp ?ε__lift ?τ ?ρ) *)
          (ewp ?s ?E ?ρ ?e ?Φ)
         =>
        first [ reshape_expr e ltac:(fun K e' => unify e' efoc; ewp_bind_core K)
              | fail 1 "ewp_bind: cannot find" efoc "in" e ]
    | _ => fail "ewp_bind: not a 'wp'"
  end.

  

Section Test.
  Context `{EM: ExecutionModel heap_lang M__glob}.
  Context `{hGS: @heapGS Σ _ EM}.
  (* Let eGS := heap_fairnessGS. *)

  Context {M: FairModel}.
  Context {msi: fmstate M -> iProp Σ}.
  Context {lifted_roles: fmstate M -> gset (fmrole M)}.
  Let step_restr st1 st2 := lifted_roles st2 ⊆ lifted_roles st1. 

  Let PI (p: state heap_lang) := gen_heap_interp p.(heap). 

  Let ewp'_instance_helper := ewp' (PI := PI) (MSI := msi) (step_restr := step_restr).  
  Existing Instance ewp'_instance_helper. 
  
  Definition prog: expr heap_lang :=
    let: "x" := ref #2 in
    "x" <- #1. 

  Lemma bind_test s E ρ: ⊢ ewp s E ρ prog (fun _ => False).
  Proof. 
    iStartProof. rewrite /prog.
    ewp_bind (ref #2)%E.
  Abort. 

End Test.
