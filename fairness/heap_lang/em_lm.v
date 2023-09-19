From trillium.fairness Require Export fairness resources fair_termination fuel fuel_ext. 
(* From trillium.fairness.heap_lang Require Export lang heap_lang_defs. *)
From iris.proofmode Require Import tactics.
From trillium.fairness Require Export partial_ownership.
From trillium.fairness Require Import execution_model.

Section LMExecModel.
  Context `{LM:LiveModel (locale Λ) M LSI}.
  Context `{CNT_Λ: Countable (locale Λ)}. 

  (* TODO: remove *)
  Context (τ0: locale Λ). 
  Hypothesis (INITτ0: forall e, locales_of_list [e] = [τ0]). 

Definition LM_init_resource `{!fairnessGS LM Σ}
   (s1: LM)
  (* FR *)
  : iProp Σ :=
  frag_model_is s1 ∗
  (∃ FR, frag_free_roles_are (FR ∖ live_roles _ s1)) ∗
  has_fuels (Σ := Σ) τ0 (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1))
  (PMPP := ActualOwnershipPartialPre). 

Definition init_thread_post `{!fairnessGS LM Σ}
  (tid: locale Λ): iProp Σ :=
  (* tid ↦M ∅. *)
  frag_mapping_is {[ tid := ∅ ]}.

Definition lm_model_init (δ: mstate LM) :=
  ls_fuel δ = gset_to_gmap (lm_fl LM δ) (live_roles _ (ls_under δ)) /\
  (* ls_mapping δ = gset_to_gmap 0%nat (live_roles _ (ls_under δ)).  *)
  ls_tmap δ (LM := LM) = {[ τ0 := live_roles _ (ls_under δ) ]}. 

Definition lm_cfg_init (σ: cfg Λ) :=
  exists (e: expr Λ), σ.1 = [e].

Definition lm_is_init_st σ s := 
  lm_cfg_init σ /\ lm_model_init s. 

Definition tids_restrict `{M: FairModel} `{Countable (locale Λ)}
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
  eapply (ls_mapping_tmap_corr (LM := LM)) in H0 as [R [? ?]].
  congruence. 
Qed. 

Definition em_lm_msi `{!fairnessGS LM Σ}
  (c: cfg Λ) (δ: mstate LM): iProp Σ :=
  model_state_interp δ ∗ ⌜ tids_restrict c (ls_tmap δ (LM := LM)) ⌝. 

(* TODO: how to make 'heap..' instantiations less wordy? *)
(* TODO: how to avoid different instances of EqDec and Cnt? *)
Lemma init_fairnessGS_LM Σ
  (* `{hPre: @fairnessGpreS (locale Λ) M LM Σ Nat.eq_dec nat_countable} *)
  `{hPre: @fairnessGpreS (locale Λ) M LSI LM Σ _ CNT_Λ}

  (* `(LM:LiveModel Λ M)   *)
  (s1: LM) (σ1 : cfg Λ) (INIT: lm_is_init_st σ1 s1):
  ⊢ (|==> ∃ fGS: fairnessGS LM Σ, (* TODO: what is a canonical way of doing it? *)
       (* ∀ `{hGS: @heapGS Σ _ (@LM_EM _ LM)}, *)
       (*   ⌜ hGS.(heap_fairnessGS) = fGS⌝ → *)
      LM_init_resource s1 ∗ em_lm_msi σ1 s1).
Proof.
  iIntros. 
  destruct INIT as [[??] [FUEL TMAP]]. destruct σ1 as [tp ?]. simpl in *. subst.

  iMod (lm_msi_init s1 ∅) as (fG) "(MSI & Hmodf & Hmapf & Hfuelf & Hfr)".
  { set_solver. } (* TODO: generalize to arbitrary set *)
  
  (* iMod (model_state_init s1) as (γmod) "[Hmoda Hmodf]". *)
  (* iMod (model_mapping_init s1) as (γmap) "[Hmapa Hmapf]". *)
  (* iMod (model_fuel_init s1) as (γfuel) "[Hfuela Hfuelf]". *)
  (* (* iMod (model_free_roles_init s1 (FR ∖ live_roles _ s1)) as (γfr) "[HFR Hfr]". *) *)
  (* iMod (model_free_roles_init s1 ∅) as (γfr) "[HFR Hfr]". *)
  iModIntro.
  iExists fG. 
  rewrite /em_lm_msi. iFrame "MSI". 
  
  (* iApply bi.sep_comm.  rewrite -bi.sep_assoc.   *)
  (* iSplitR "Hmodf Hfr Hfuelf Hmapf". *)
  (* 1: { unfold model_state_interp. simpl. iFrame.  *)
  (*      iExists _. *)

  (*      iSplitL "Hfuela". *)
  (*      { rewrite /auth_fuel_is /=. *)
  (*        rewrite FUEL. rewrite fmap_gset_to_gmap //. }  *)

  (*      iSplitL "Hmapa"; first by rewrite TMAP /auth_mapping_is /= map_fmap_singleton //. *)
  (*      iSplit; first done. *)
  (*      (* - intros ρ tid. rewrite MAP.  *) *)
  (*      (*   rewrite lookup_gset_to_gmap_Some. *) *)
  (*      (*   setoid_rewrite lookup_singleton_Some. split; naive_solver. *) *)

  (*      (* - rewrite FUEL. rewrite dom_gset_to_gmap. set_solver. *) *)
  (*      iPureIntro. set_solver.  *)
  (* } *)

  iSplitL.
  2: { iPureIntro. rewrite /tids_restrict.
       intros tid Hlocs. rewrite TMAP lookup_singleton_ne //.
       (* compute in Hlocs. *)
       simpl in Hlocs. rewrite INITτ0 in Hlocs. 
       set_solver. }

  rewrite /LM_init_resource /has_fuels /=.
  rewrite dom_gset_to_gmap. rewrite FUEL TMAP. iFrame.
  iSplitL "Hfr".
  { rewrite /frag_free_roles_are. 
    iExists ∅. rewrite subseteq_empty_difference_L; set_solver. }

  unfold frag_fuel_is.
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


Global Instance LM_EM: @ExecutionModel Λ LM.
refine
  {|
    em_preGS := fun Σ => fairnessGpreS LM Σ;
    em_GS := fun Σ => fairnessGS LM Σ;
    em_Σ := fairnessΣ (locale Λ) M;
    em_Σ_subG := fun Σ => @subG_fairnessGpreS _ _ _ _ LM _ _;

    (* em_valid_evolution_step := valid_evolution_step (LM := LM); *)
    em_thread_post Σ := fun {_: fairnessGS LM Σ} (tid: locale Λ) => 
                          (* tid ↦M ∅; *)
                          frag_mapping_is {[ tid := ∅ ]};
    (* TODO: cannot express the msi instantiation this way*)
    (* em_msi Σ := fun {_: fairnessGS LM Σ} es δ => model_state_interp es δ (LM := LM); *)
    em_is_init_st := lm_is_init_st;

    em_init_resource Σ := fun {_: fairnessGS LM Σ} δ => LM_init_resource δ;
|}.
(* TODO: cannot directly specify these components *)
Unshelve. 
{ exact (valid_evolution_step (LM := LM)). }
2: { intros ? fG. exact (em_lm_msi (fairnessGS0 := fG)). } 
intros. iIntros. iMod (init_fairnessGS_LM _ s1 σ) as "[% [? X]]"; [done| ]. 
iModIntro. iExists _. iFrame. 
Defined. 

End LMExecModel.
