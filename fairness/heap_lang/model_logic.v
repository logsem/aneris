From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap.
From trillium.fairness.heap_lang Require Import tactics notation sswp_logic.
From trillium.fairness Require Import fairness resources fuel model_plug lm_fair.

Section ModelLogic.

  Context `{EM: ExecutionModel heap_lang M__glob}.   
  Context `{hGS: @heapGS Σ _ EM}.
  Let eGS := heap_fairnessGS.

  Context {M: FairModel}.
  Context {msi: fmstate M -> iProp Σ}. 

  Let CWP := @cwp _ _ EM _ eGS _ msi _. 

  Lemma cwp_model_sswp_step s tid ρ E ε__lift e Φ P Q:
    TCEq (to_val e) None →
    ε__lift ⊆ E ->
    local_rule (msi := msi) P Q ρ -∗
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

Section ModelLogic.
  Set Default Proof Using "Type".

  Context `{EM: ExecutionModel heap_lang M}.   
  Context `{hGS: @heapGS Σ _ EM}.
  Let eGS := heap_fairnessGS.

  Context `{Countable G}.
  Context `{iLM: LiveModel G iM LSI}.
  Context {LFP: LMFairPre iLM}.
  Let LF := LM_Fair (LF := LFP). 
  Context {fGS: @fairnessGS _ _ _ _ _ iLM Σ}. 

  Let CWP := @cwp _ _ EM _ eGS LF (model_state_interp (LM := iLM)) _. 
  
  Notation "tid ↦M R" := (partial_mapping_is {[ tid := R ]}) (at level 33).
  Notation "tid ↦m ρ" := (partial_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
  Notation "ρ ↦F f" := (partial_fuel_is {[ ρ := f ]}) (at level 33).


  

Lemma wp_step_model s tid ρ (f1 : nat) fs fr s1 s2 E ε__lift e Φ (g: G):
  TCEq (to_val e) None →
  fmtrans iM s1 (Some ρ) s2 →
  iM.(live_roles) s2 ⊆ iM.(live_roles) s1 →
  ρ ∉ dom fs →
  ▷ frag_model_is s1 -∗
  ▷ has_fuels g ↦M ({[ρ:=f1]} ∪ fmap S fs) -∗
  ▷ frag_free_roles_are fr -∗
  sswp s E e (λ e', frag_model_is s2 -∗
                    g ↦M ({[ρ:=(iLM.(lm_fl) s2)]} ∪ fs) -∗
                    frag_free_roles_are fr -∗
                    WP e' @ s; tid; E {{ Φ }} ) -∗
  (* WP e @ s; tid; E {{ Φ }}. *)
  CWP e Φ s E ε__lift tid g.
Proof.
  iIntros (Hval Htrans Hlive Hdom) ">Hst >Hfuel1 >Hfr Hwp".
  rewrite wp_unfold /wp_pre.
  rewrite /sswp. simpl. rewrite Hval.
  iIntros (extr atr K tp1 tp2 σ1 Hvalid Hloc Hexend) "(% & Hsi & Hmi)".
  iMod ("Hwp" with "Hsi") as (Hred) "Hwp". iIntros "!>".
  iSplitR; [by rewrite Hexend in Hred|]. iIntros (????). rewrite Hexend.
  iMod ("Hwp" with "[//]") as "Hwp". iIntros "!>!>". iMod "Hwp". iIntros "!>".
  iApply step_fupdN_intro; [done|]. iIntros "!>".
  iMod "Hwp" as "[Hσ [Hwp ->]]".
  iDestruct (model_agree' with "Hmi Hst") as %Hmeq. iFrame.
  rewrite /trace_ends_in in Hexend. rewrite -Hexend.
  iMod (update_model_step with "Hfuel1 Hst Hmi") as
    (δ2 Hvse) "(Hfuel & Hst & Hmod)"; eauto.
  - rewrite -Hloc. eapply locale_step_atomic; eauto. by apply fill_step.
  - iModIntro; iExists δ2, (Take_step ρ tid). rewrite big_sepL_nil. iFrame.
    iSplit; [done|]. iDestruct ("Hwp" with "Hst Hfuel Hfr") as "Hwp". by iFrame.
Qed.


End ModelLogic.
