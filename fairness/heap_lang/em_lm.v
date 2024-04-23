From trillium.fairness Require Export fairness resources fair_termination fuel. 
(* From trillium.fairness.heap_lang Require Export lang heap_lang_defs. *)
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import execution_model lm_fair_traces lm_fair model_plug lm_restr_gen. 

Section LMExecModel.
  Context `{CNT_Λ: Countable (locale Λ)}.
  Context `{LM:LiveModel (locale Λ) M LSI}.
  Context {LF: LMFairPre LM}. 
  
  (* TODO: remove *)
  Context (τ0: locale Λ). 
  Hypothesis (INITτ0: forall e, locales_of_list [e] = [τ0]). 

  Definition LM_init_resource `{!fairnessGS LM Σ}
    (s1: LM)
    FR
    : iProp Σ :=
    frag_model_is s1 ∗
      (frag_free_roles_are (FR ∖ live_roles _ s1)) ∗
      has_fuels (Σ := Σ) τ0 (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1)). 
  
Definition init_thread_post `{!fairnessGS LM Σ}
  (tid: locale Λ): iProp Σ :=
  (* tid ↦M ∅. *)
  frag_mapping_is {[ tid := ∅ ]}.

Definition lm_model_init (δ: mstate LM) :=
  ls_fuel δ = gset_to_gmap (lm_fl LM δ) (live_roles _ (ls_under δ)) /\
  (* ls_mapping δ = gset_to_gmap 0%nat (live_roles _ (ls_under δ)).  *)
  ls_tmap δ = {[ τ0 := live_roles _ (ls_under δ) ]}. 

Definition lm_cfg_init (σ: cfg Λ) :=
  exists (e: expr Λ), σ.1 = [e].

Definition lm_is_init_st σ s := 
  lm_cfg_init σ /\ lm_model_init s. 

Definition tids_restrict `{M: FairModel}
  (c: cfg Λ) (tmap: gmap (locale Λ) (gset (fmrole M))): Prop :=
  forall ζ, ζ ∉ locales_of_list c.1 → tmap !! ζ = None.

(* TODO: unify with existing locales_of_list_from_locale_from, 
   remove restriction for Λ *)
Lemma locales_of_list_from_locale_from' tp0 tp1 ζ:
  ζ ∈ locales_of_list_from tp0 tp1 (Λ := Λ) ->
  is_Some (from_locale_from tp0 tp1 ζ).
Proof.
  clear -tp0 tp1 ζ.
  revert tp0; induction tp1 as [|e1 tp1 IH]; intros tp0.
  { simpl. intros H. inversion H. }
  simpl.
  rewrite /locales_of_list_from /=. intros.
  destruct (decide (locale_of tp0 e1 = ζ)); simplify_eq; first set_solver.
  apply elem_of_cons in H as [?| ?]; [done| ].
  set_solver.
Qed.

Lemma tids_restrict_smaller (σ: cfg Λ) (δ: lm_ls LM):
  tids_restrict σ (ls_tmap δ) -> tids_smaller σ.1 δ.
Proof.
  rewrite /tids_smaller /tids_restrict. 
  intros. apply locales_of_list_from_locale_from'.
  destruct (decide (ζ ∈ locales_of_list σ.1)); [done| ].
  specialize (H _ n).
  eapply (ls_mapping_tmap_corr) in H0 as [R [? ?]].
  congruence. 
Qed.

(* TODO: get rid of one of these definitions *)
Lemma tids_restrict_smaller' (σ: cfg Λ) (δ: lm_ls LM):
  tids_restrict σ (ls_tmap δ) -> tids_smaller' σ.1 δ.
Proof.
  rewrite /tids_smaller' /tids_restrict. 
  intros. apply locales_of_list_from_locale_from'.
  destruct (decide (ζ ∈ locales_of_list σ.1)); [done| ].
  specialize (H _ n).
  apply elem_of_dom in H0 as [? ?]. congruence. 
Qed.
Lemma tids_smaller'_restrict (σ: cfg Λ) (δ: lm_ls LM):
  tids_smaller' σ.1 δ -> tids_restrict σ (ls_tmap δ).
Proof.
  rewrite /tids_smaller' /tids_restrict. 
  intros. destruct (ls_tmap δ !! ζ) eqn:T; [| done].
  specialize (H _ (ltac:(apply elem_of_dom; done))).
  by apply locales_of_list_from_locale_from in H. 
Qed.



Definition em_lm_msi `{!fairnessGS LM Σ}
  (c: cfg Λ) (δ: mstate LM): iProp Σ :=
  model_state_interp δ ∗ ⌜ tids_restrict c (ls_tmap δ) ⌝. 

(* TODO: how to make 'heap..' instantiations less wordy? *)
(* TODO: how to avoid different instances of EqDec and Cnt? *)
Lemma init_fairnessGS_LM Σ
  {hPre: @fairnessGpreS (locale Λ) _ _ M LSI LM Σ}
  (s1: LM) (σ1 : cfg Λ) FR (INIT: lm_is_init_st σ1 s1):
  ⊢ (|==> ∃ fGS: fairnessGS LM Σ, (* TODO: what is a canonical way of doing it? *)
         LM_init_resource s1 (FR ∖ dom (ls_fuel s1)) ∗ em_lm_msi σ1 s1).
Proof.
  iIntros.
  destruct INIT as [[??] [FUEL TMAP]]. destruct σ1 as [tp ?]. simpl in *. subst.

  iMod (lm_msi_init s1 (FR ∖ dom (ls_fuel s1))) as (fG) "(MSI & Hmodf & Hmapf & Hfuelf & Hfr)".
  { set_solver. } (* TODO: generalize to arbitrary set *)
  
  iModIntro.
  iExists fG. 
  rewrite /em_lm_msi. iFrame "MSI". 
  
  iSplitL.
  2: { iPureIntro. rewrite /tids_restrict.
       intros tid Hlocs. rewrite TMAP lookup_singleton_ne //.
       (* compute in Hlocs. *)
       simpl in Hlocs. rewrite INITτ0 in Hlocs. 
       set_solver. }

  rewrite /LM_init_resource /has_fuels /=.
  rewrite dom_gset_to_gmap. rewrite FUEL TMAP. iFrame.
  iSplitL "Hfr".
  { iApply frag_free_roles_are_proper; [| by iFrame].
    rewrite dom_gset_to_gmap. set_solver. }

  unfold partial_fuel_is, frag_fuel_is.
  setoid_rewrite map_fmap_singleton.
  simpl.
  destruct (decide (live_roles M s1 = ∅)) as [-> | NE].
  { by iApply big_sepS_empty. }
  iDestruct (own_proper with "Hfuelf") as "Hfuelf".
  { apply auth_frag_proper. rewrite fmap_gset_to_gmap. 
    apply @gset_to_gmap_singletons. } 
  rewrite big_opS_auth_frag. rewrite big_opS_own; [| done].
  iApply (big_sepS_mono with "Hfuelf"). iIntros (ρ Hin) "H".
  iExists _. iFrame. iPureIntro. apply lookup_gset_to_gmap_Some. done.
Qed.

Global Instance LM_EM: @ExecutionModel Λ (fair_model_model (LM_Fair)).
refine
  {|
    em_preGS := fun Σ => fairnessGpreS LM Σ;
    em_GS := fun Σ => fairnessGS LM Σ;
    em_Σ := fairnessΣ (locale Λ) M;
    em_Σ_subG := fun Σ => @subG_fairnessGpreS _ _ _ _ _ _ LM;

    (* em_valid_evolution_step := valid_evolution_step (LM := LM); *)
    em_thread_post Σ := fun {_: fairnessGS LM Σ} (tid: locale Λ) =>
                          (* tid ↦M ∅; *)
                          frag_mapping_is {[ tid := ∅ ]};
    (* TODO: cannot express the msi instantiation this way*)
    (* em_msi Σ := fun {_: fairnessGS LM Σ} es δ => model_state_interp es δ (LM := LM); *)
    em_init_param := gset (fmrole M);
    em_is_init_st := (@lm_is_init_st: cfg Λ -> mstate (fair_model_model (LM_Fair)) -> Prop);

    em_init_resource Σ := fun {_: fairnessGS LM Σ} (δ: mstate (fair_model_model (LM_Fair))) FR => LM_init_resource δ (FR ∖ dom (ls_fuel δ));
|}.
(* TODO: cannot directly specify these components *)
Unshelve. 
{ exact (valid_evolution_step (LM := LM)). }
2: { intros ? fG. exact (em_lm_msi (fairnessGS0 := fG)). } 
intros. iIntros. iMod (init_fairnessGS_LM _ s1 σ) as "[% [? X]]"; [done| ]. 
iModIntro. iExists _. iFrame. 
Defined. 


Section RoleLiftLM.
  Context {Σ: gFunctors}.
  Context {fG: fairnessGS LM Σ}.
  Context {INV: invGS_gen HasNoLc Σ}.

  Context {RESTR: forall g δ, enabled_group_nonempty g δ (LM := LM)}. 

  Let lr: fmstate LM_Fair -> gset (fmrole LM_Fair) :=
        fun δ => filter (flip role_enabled_model δ) (dom (ls_tmap δ)).

  Let RL := @role_lift _ _ LM_EM _ fG LM_Fair model_state_interp lr INV.

  (* TODO: move *)
  Lemma LM_step_ngn `{Countable G'} `{LM': LiveModel G' M' LSI'}:
    forall δ1 ℓ δ2, lm_ls_trans LM' δ1 ℓ δ2 -> new_groups_nonempty δ1 δ2. 
  Proof. 
    intros δ1 ℓ δ2 STEP.
    destruct ℓ; try by apply STEP. set_solver.
  Qed. 

  (* TODO: move *)
  Lemma LM_step_groups `{Countable G'} `{LM': LiveModel G' M' LSI'}:
    forall δ1 ℓ δ2, lm_ls_trans LM' δ1 ℓ δ2 ->
               forall g R, ls_tmap δ2 !! g = Some R -> R ≠ ∅ \/ g ∈ dom (ls_tmap δ1).
  Proof. 
    intros δ1 ℓ δ2 STEP g R TM2.
    destruct (decide (R = ∅)); [| tauto]. subst. right.
    destruct (decide (g ∈ dom (ls_tmap δ1))); [done| ]. 
    apply LM_step_ngn in STEP. red in STEP. specialize_full STEP.
    { apply elem_of_difference. split; eauto.
      eapply elem_of_dom. eauto. }
    by rewrite TM2 in STEP.
  Qed. 

  Lemma TopRL τ: ⊢ RL ∅ τ τ ⌜ True ⌝.
  Proof.
    rewrite /RL /role_lift. iIntros (P Q) "!# #RULE".
    iIntros (etr atr c2) "(_&P&SI&%STEP)".
    simpl. rewrite /em_lm_msi. iDestruct "SI" as "[MSI %TR]".
    rewrite /valid_evolution_step.
    iMod ("RULE" with "[$]") as (δ2) "(Q&MSI&%TRANS&%LR)".
    iModIntro. do 2 iExists _. iFrame. iPureIntro.
    apply and_comm. rewrite -!and_assoc. split; [| split].
    1, 2: by eauto. 
    apply iff_and_impl_helper.
    { apply tids_smaller'_restrict. }
    
    red. intros τ' D2.
    destruct (decide (τ' ∈ dom (ls_tmap (trace_last atr)))) as [D1 | ND1].
    { destruct (trace_last etr), c2. 
      apply tids_restrict_smaller' in TR. apply TR in D1. 
      eapply from_locale_step; eauto. }
    destruct TRANS as (?&TRANS&?).
    apply elem_of_dom in D2 as [R' TM']. 
    eapply LM_step_groups in TRANS as [NEQ| ?]; eauto; [| done].
    specialize (LR τ'). specialize_full LR.
    { rewrite /lr. apply elem_of_filter. split.
      - red. apply RESTR. rewrite TM'. done.
      - eapply elem_of_dom; eauto. }
    destruct ND1. rewrite /lr in LR. apply elem_of_filter in LR. apply LR.
  Qed. 

End RoleLiftLM.

End LMExecModel.
