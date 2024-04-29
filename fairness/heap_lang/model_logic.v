From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap.
From trillium.fairness.heap_lang Require Import tactics notation sswp_logic.
From trillium.fairness Require Import fairness resources fuel model_plug lm_fair.
From trillium.fairness.lm_rules Require Import model_step resources_updates fuel_step.


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
  Hypothesis (IMPL_LIFT: forall (δ δ': fmstate LF),
                 dom (ls_tmap δ') = dom (ls_tmap δ) ->
                 live_roles _ δ' ⊆ live_roles _ δ ->
                 lifted_roles δ' ⊆ lifted_roles δ).
  Hypothesis (TRANS_NO_ENAB: forall δ g δ',
                 locale_trans δ g δ' (LM := iLM) ->
                 live_roles LF δ' ⊆ live_roles LF δ). 
  
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
    apply IMPL_LIFT.
    - rewrite TM. rewrite dom_insert_L. 
      apply locale_trans_dom in STEP'. clear -STEP'. set_solver.
    - eapply TRANS_NO_ENAB. apply STEP'.
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
    apply IMPL_LIFT.
    - by rewrite TM.
    - eapply TRANS_NO_ENAB. apply STEP'.
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
    apply IMPL_LIFT.
    - rewrite TM. rewrite dom_insert_L. 
      apply locale_trans_dom in STEP'. clear -STEP'. set_solver.
    - eapply TRANS_NO_ENAB. apply STEP'.
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

  Lemma cwp_model_sswp_step s tid ρ E ε__lift e Φ P Q:
    TCEq (to_val e) None →
    ε__lift ⊆ E ->
    local_rule (msi := msi) (lifted_roles := lifted_roles) P Q ρ -∗
    ▷ P -∗
    sswp s E e (λ e', Q -∗ CWP e' Φ s E ε__lift tid ρ) -∗
    CWP e Φ s E ε__lift tid ρ.
  Proof.
    iIntros (Hval SUBM) "#RULE P SSWP". 
    rewrite /CWP /cwp. iIntros (LC) "LC #LIFT".
    
    rewrite wp_unfold /wp_pre. rewrite /sswp. simpl. rewrite Hval.
    iIntros (extr atr K tp1 tp2 σ1 Hvalid Hloc Hexend) "(% & Hsi & Hmi)".

    iMod ("SSWP" with "Hsi") as (Hred) "Hwp". iIntros "!>".
    iSplitR; [by rewrite Hexend in Hred|]. iIntros (????). rewrite Hexend.
    iMod ("Hwp" with "[//]") as "Hwp". iIntros "!>!>". iMod "Hwp". iIntros "!>".
    iApply step_fupdN_intro; [done|]. iIntros "!>".
    iMod "Hwp" as "[Hσ [Hwp ->]]".
    rewrite /trace_ends_in in Hexend. rewrite -Hexend.

    iApply fupd_mask_mono; eauto.
    rewrite /role_lift.
    iMod ("LIFT" with "RULE [LC P Hmi]") as (δ2 ℓ) "(LC & Q & MSI & %EV)". 
    { iFrame. iPureIntro.
      rewrite -Hloc. eapply locale_step_atomic; eauto. by apply fill_step. }

    iSpecialize ("Hwp" with "Q LC [$]"). 
    iModIntro. do 2 iExists _. iFrame.
    iSplit; done.
  Qed.

  Lemma cwp_value s E ε__lift Φ ζ ρ e v : IntoVal e v → Φ v ⊢ CWP e Φ s E ε__lift ζ ρ.
  Proof.
    rewrite /CWP /cwp. iIntros (?) "? % ??".
    iApply wp_value. iFrame.
  Qed.

End ModelLogic.


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

Lemma wp_step_model s tid ρ (f1 : nat) fs fr s1 s2 E ε__lift e Φ (g: G):
  TCEq (to_val e) None →
  fmtrans iM s1 (Some ρ) s2 →
  ε__lift ⊆ E ->
  iM.(live_roles) s2 ⊆ iM.(live_roles) s1 →
  ρ ∉ dom fs →
  ▷ frag_model_is s1 -∗
  ▷ has_fuels g ({[ρ:=f1]} ∪ fmap S fs) -∗
  ▷ frag_free_roles_are fr -∗
  sswp s E e (λ e', frag_model_is s2 -∗
                    has_fuels g ({[ρ:=(iLM.(lm_fl) s2)]} ∪ fs) -∗
                    frag_free_roles_are fr -∗
                    CWP e' Φ s E ε__lift tid g) -∗
  (* WP e @ s; tid; E {{ Φ }}. *)
  CWP e Φ s E ε__lift tid g.
Proof.
  iIntros (Hval Htrans INV Hlive Hdom).
  (* iIntros ">Hst >Hfuel1 >Hfr Hwp".  *)
  iIntros "Hst Hfuel1 Hfr Hwp".

  (* TODO: get rid of this explicit specialization *)
  pose proof cwp_model_sswp_step (msi := msi) (lifted_roles := lr) as STEP.
  iApply (STEP with "[] [-Hwp] [Hwp]"); [by apply INV|..].
  { iApply model_step_local_rule. 
  (* 2: { iNext. iAccu. } *)
  (* { rewrite /local_rule. iModIntro. iIntros (?) "[(ST & FUELS & FREE) MSI]". *)
  (*   iMod (actual_update_step_still_alive_gen with "[$] [$] [$] [$]") as (δ') "RES". *)
  (*   4: { apply intersection_empty_r_L. } *)
  (*   4: { apply Htrans. } *)
  (*   2, 3: set_solver.  *)
Abort.


End Test.
