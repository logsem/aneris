From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap.
From trillium.fairness.heap_lang Require Import tactics notation sswp_logic.
From trillium.fairness Require Import fairness resources fuel model_plug lm_fair.
From trillium.fairness.lm_rules Require Import model_step resources_updates fuel_step.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.


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
  Let eGS := heap_fairnessGS.

  Context {M: FairModel}.
  Context {msi: fmstate M -> iProp Σ}. 
  Context {lifted_roles: fmstate M -> gset (fmrole M)}.

  Let CWP := @cwp _ _ EM _ eGS _ msi lifted_roles _.
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
      (* WP e Φ s E ε__lift tid ρ. *)
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
    (* iMod ("Hsswp" with "[//] [//] [//] Hσ") as (Hs) "Hsswp". *)
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
    (* iApply (step_fupdN_wand with "Hsswp"). *)
    iMod "Hsswp" as "(Hσ & HMU & ->)". iFrame. 

    (* rewrite -Hextr. *)
    (* iSpecialize ("HMU" with "MSI").  *)
    iMod ("HMU" with "MSI []") as (??) "(Hσ & %EV' & Hwp)".
    { iPureIntro. rewrite -Hζ. 
      econstructor; eauto. rewrite Hζ.
      eapply fill_prim_step; eauto. }
    iMod "CLOS'" as "_". 
    iMod "Hwp". iModIntro.
    iExists _, _. simpl in *. rewrite right_id_L. simpl. iFrame.
    iPureIntro. simpl in *. rewrite right_id_L in EV'. done. 
  Qed.

  (* Lemma sswp_MU_wp s tid E ε__lift e Φ: *)
  (*   (sswp s ε__lift e  *)
  (*                (λ e', MU ε__lift tid ((WP e' @ s; tid; E {{ Φ }})) (eGS := heap_fairnessGS)))%I -∗ *)
  (*     (* WP e Φ s E ε__lift tid ρ. *) *)
  (*     WP e @ s; tid; E {{ Φ }}.  *)
  (* Proof. *)
  (*   iIntros "Hsswp". iApply sswp_MU_wp_fupd. iModIntro. *)
  (*   iApply (sswp_wand with "[] Hsswp"). *)
  (* iIntros (??) "HMU". iApply (MU_wand with "[] HMU"). by iIntros "$ !>". *)
  (*   done.  *)

  Lemma sswp_MU_cwp_fupd s tid ρ E ε__lift E' e Φ
    (SUB': ε__lift ⊆ E'):
    (|={E, E'}=> sswp s ε__lift e 
                 (λ e', lmu ρ (|={E',E}=> CWP e' Φ s E ε__lift tid ρ)))%I -∗
      CWP e Φ s E ε__lift tid ρ.
  Proof.
    rewrite /CWP /cwp.
    iIntros "Hsswp". iIntros (LC) "LC #LU".

    iApply sswp_MU_wp_fupd; [apply SUB'|]. iMod "Hsswp". iModIntro.
    iApply (sswp_wand with "[-Hsswp]"); [| by iFrame].
    simpl. clear e. iIntros (e) "LMU".
    iPoseProof ("LU" with "LMU LC") as "MU". 
    iApply (MU_mono with "[-MU] MU").
    iIntros "[LIFT LC]". iMod "LIFT". iModIntro.    
    iApply ("LIFT" with "LC [$]").
  Qed. 

  Lemma sswp_MU_cwp s tid ρ E ε__lift e Φ
    (SUB: ε__lift ⊆ E):
    (sswp s ε__lift e 
                 (λ e', lmu ρ (CWP e' Φ s E ε__lift tid ρ)))%I -∗
      CWP e Φ s E ε__lift tid ρ.
  Proof.
    iIntros "Hsswp".
    iApply sswp_MU_cwp_fupd; [apply SUB| ]. iModIntro.     
    iApply (sswp_wand with "[-Hsswp]"); [| by iFrame].
    iIntros. iApply LMU_mono; [| by iFrame]. intuition.
  Qed.       

  Lemma cwp_value s E ε__lift Φ ζ ρ e v : IntoVal e v → Φ v ⊢ CWP e Φ s E ε__lift ζ ρ.
  Proof.
    rewrite /CWP /cwp. iIntros (?) "? % ??".
    iApply wp_value. iFrame.
  Qed.

Section Tactics.

    (* From trillium.program_logic Require Import ectxi_language.  *)

  Lemma tac_cwp_bind
    (* K Δ s E Φ e f : *)
    (* f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *) *)
    (* envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I → *)
    (* envs_entails Δ (WP fill K e @ s; E {{ Φ }}). *)
K Δ (e: expr heap_lang) (Φ: val heap_lang -> iProp Σ) (s: stuckness) (ε__wp ε__lift: coPset) (τ: locale heap_lang) (ρ: fmrole M) f:
    f = (λ e, fill K e) ->
      envs_entails Δ (CWP e (fun v => CWP (f (Val v)) Φ s ε__wp ε__lift τ ρ) s ε__wp ε__lift τ ρ) ->
      envs_entails Δ (CWP (fill K e) Φ s ε__wp ε__lift τ ρ). 
  Proof. rewrite envs_entails_unseal=> -> ->. by apply: cwp_bind. Qed.

End Tactics.

End ModelLogic.

  Ltac cwp_bind_core K :=
    lazymatch eval hnf in K with
    | [] => idtac
    | _ => eapply (tac_cwp_bind K); [simpl; reflexivity|reduction.pm_prettify]
    end.

  Tactic Notation "cwp_bind" open_constr(efoc) :=
    iStartProof;
    lazymatch goal with
    | |- envs_entails _
          (* (wp ?s ?E ?locale ?e ?Q) *)
          (cwp ?e ?Φ ?s ?ε__wp ?ε__lift ?τ ?ρ)
         =>
        first [ reshape_expr e ltac:(fun K e' => unify e' efoc; cwp_bind_core K)
              | fail 1 "cwp_bind: cannot find" efoc "in" e ]
    | _ => fail "cwp_bind: not a 'wp'"
  end.

  


Section Test.
  Context `{EM: ExecutionModel heap_lang M}.   
  Context `{hGS: @heapGS Σ _ EM}.
  Let eGS := heap_fairnessGS.

  Context `{Countable G}.
  Context `{iLM: LiveModel G iM LSI}.
  Context {LFP: LMFairPre iLM}.
  Let LF := LM_Fair (LF := LFP). 
  Context {fGS: @fairnessGS _ _ _ _ _ iLM Σ}. 

  Let msi: fmstate LF -> iProp Σ := model_state_interp (LM := iLM).
  Let lr: fmstate LF -> gset (fmrole LF) :=
        fun δ => filter (flip role_enabled_model δ) (dom (ls_tmap δ)).
  
  Let CWP := @cwp _ _ EM _ eGS LF msi lr _. 
  
  Notation "tid ↦M R" := (partial_mapping_is {[ tid := R ]}) (at level 33).
  Notation "tid ↦m ρ" := (partial_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
  Notation "ρ ↦F f" := (partial_fuel_is {[ ρ := f ]}) (at level 33).

  Definition prog: expr heap_lang :=
    let: "x" := ref #2 in
    "x" <- #1. 

  Lemma bind_test s E ε__lift tid g: ⊢ CWP prog (fun _ => ⌜ False ⌝) s E ε__lift tid g.
  Proof. 
    iStartProof. rewrite /prog.
    rewrite /CWP.
    cwp_bind (ref #2)%E.
  Abort. 

(* Lemma wp_step_model s tid ρ (f1 : nat) fs fr s1 s2 E ε__lift e Φ (g: G): *)
(*   TCEq (to_val e) None → *)
(*   fmtrans iM s1 (Some ρ) s2 → *)
(*   ε__lift ⊆ E -> *)
(*   iM.(live_roles) s2 ⊆ iM.(live_roles) s1 → *)
(*   ρ ∉ dom fs → *)
(*   ▷ frag_model_is s1 -∗ *)
(*   ▷ has_fuels g ({[ρ:=f1]} ∪ fmap S fs) -∗ *)
(*   ▷ frag_free_roles_are fr -∗ *)
(*   sswp s E e (λ e', frag_model_is s2 -∗ *)
(*                     has_fuels g ({[ρ:=(iLM.(lm_fl) s2)]} ∪ fs) -∗ *)
(*                     frag_free_roles_are fr -∗ *)
(*                     CWP e' Φ s E ε__lift tid g) -∗ *)
(*   (* WP e @ s; tid; E {{ Φ }}. *) *)
(*   CWP e Φ s E ε__lift tid g. *)
(* Proof. *)
(*   iIntros (Hval Htrans INV Hlive Hdom). *)
(*   (* iIntros ">Hst >Hfuel1 >Hfr Hwp".  *) *)
(*   iIntros "Hst Hfuel1 Hfr Hwp". *)

(*   (* TODO: get rid of this explicit specialization *) *)
(*   pose proof cwp_model_sswp_step (msi := msi) (lifted_roles := lr) as STEP. *)
(*   iApply (STEP with "[] [-Hwp] [Hwp]"); [by apply INV|..]. *)
(*   { iApply model_step_local_rule.  *)
(*   (* 2: { iNext. iAccu. } *) *)
(*   (* { rewrite /local_rule. iModIntro. iIntros (?) "[(ST & FUELS & FREE) MSI]". *) *)
(*   (*   iMod (actual_update_step_still_alive_gen with "[$] [$] [$] [$]") as (δ') "RES". *) *)
(*   (*   4: { apply intersection_empty_r_L. } *) *)
(*   (*   4: { apply Htrans. } *) *)
(*   (*   2, 3: set_solver.  *) *)
(* Abort. *)


End Test.