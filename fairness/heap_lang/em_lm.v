From trillium.fairness Require Export fairness resources fair_termination fuel fuel_ext. 
From trillium.fairness.heap_lang Require Export lang heap_lang_defs.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Export actual_resources partial_ownership.


Definition LM_init_resource `{LM:LiveModel heap_lang M} `{!fairnessGS LM Σ}
   (s1: LM)
  (* FR *)
  : iProp Σ :=
  frag_model_is s1 ∗
  (∃ FR, frag_free_roles_are (FR ∖ live_roles _ s1)) ∗
  has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1))
  (PMPP := ActualOwnershipPartialPre). 

Definition init_thread_post `{LM:LiveModel heap_lang M} `{!fairnessGS LM Σ}
  (tid: locale heap_lang): iProp Σ :=
  (* tid ↦M ∅. *)
  frag_mapping_is {[ tid := ∅ ]}.

Definition lm_model_init `{LM: LiveModel heap_lang M} (δ: mstate LM) :=
  ls_fuel δ = gset_to_gmap (lm_fl LM δ) (live_roles _ (ls_under δ)) /\
  (* ls_mapping δ = gset_to_gmap 0%nat (live_roles _ (ls_under δ)).  *)
  ls_tmap δ (LM := LM) = {[ 0%nat := live_roles _ (ls_under δ) ]}. 

Definition lm_cfg_init (σ: cfg heap_lang) :=
  exists (e: expr), σ.1 = [e].

Definition lm_is_init_st `{LM: LiveModel heap_lang M} σ s := 
  lm_cfg_init σ /\ lm_model_init s (LM := LM). 

Definition tids_restrict `{M: FairModel} `{Countable (locale Λ)}
  (c: cfg Λ) (tmap: gmap (locale Λ) (gset (fmrole M))): Prop :=
  forall ζ, ζ ∉ locales_of_list c.1 → tmap !! ζ = None.

(* TODO: unify with existing locales_of_list_from_locale_from, 
   remove restriction for heap_lang *)
Lemma locales_of_list_from_locale_from' tp0 tp1 ζ:
  ζ ∈ locales_of_list_from tp0 tp1 (Λ := heap_lang) ->
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

Lemma tids_restrict_smaller `{LM:LiveModel heap_lang M} (σ: cfg heap_lang) (δ: lm_ls LM):
  tids_restrict σ (ls_tmap δ) -> tids_smaller σ.1 δ.
Proof.
  rewrite /tids_smaller /tids_restrict. 
  intros. apply locales_of_list_from_locale_from'.
  destruct (decide (ζ ∈ locales_of_list σ.1)); [done| ].
  specialize (H _ n).
  eapply (ls_mapping_tmap_corr (LM := LM)) in H0 as [R [? ?]].
  congruence. 
Qed. 

Definition em_lm_msi `{LM:LiveModel heap_lang M} `{!fairnessGS LM Σ}
  (c: cfg heap_lang) (δ: mstate LM): iProp Σ :=
  model_state_interp δ ∗ ⌜ tids_restrict c (ls_tmap δ (LM := LM)) ⌝. 

(* TODO: how to make 'heap..' instantiations less wordy? *)
(* TODO: how to avoid different instances of EqDec and Cnt? *)
Lemma init_fairnessGS_LM Σ `{hPre: @fairnessGpreS heap_lang M LM Σ
                                     Nat.eq_dec nat_countable
  }
  (* `(LM:LiveModel heap_lang M)   *)
  (s1: LM) (σ1 : cfg heap_lang) (INIT: lm_is_init_st σ1 s1):
  ⊢ (|==> ∃ fGS: fairnessGS LM Σ, (* TODO: what is a canonical way of doing it? *)
       (* ∀ `{hGS: @heapGS Σ _ (@LM_EM _ LM)}, *)
       (*   ⌜ hGS.(heap_fairnessGS) = fGS⌝ → *)
      LM_init_resource s1 ∗ em_lm_msi σ1 s1).
Proof.
  iIntros. 
  destruct INIT as [[??] [FUEL TMAP]]. destruct σ1 as [tp ?]. simpl in *. subst.
  iMod (model_state_init s1) as (γmod) "[Hmoda Hmodf]".
  iMod (model_mapping_init s1) as (γmap) "[Hmapa Hmapf]".
  iMod (model_fuel_init s1) as (γfuel) "[Hfuela Hfuelf]".
  (* TODO: seems like the concrete set of free roles doesn't matter *)
  (* iMod (model_free_roles_init s1 (FR ∖ live_roles _ s1)) as (γfr) "[HFR Hfr]". *)
  iMod (model_free_roles_init s1 ∅) as (γfr) "[HFR Hfr]".
  iModIntro.
  iExists ({| 
              fairness_inG := hPre;
              fairness_model_name := γmod;
              fairness_model_mapping_name := γmap;
              fairness_model_fuel_name := γfuel;
              fairness_model_free_roles_name := γfr;
            |}).
  
  iApply bi.sep_comm. rewrite /em_lm_msi. rewrite -bi.sep_assoc.  
  iSplitR "Hmodf Hfr Hfuelf Hmapf".
  1: { unfold model_state_interp. simpl. iFrame. 
       iExists _.

       iSplitL "Hfuela".
       { rewrite /auth_fuel_is /=.
         rewrite FUEL. rewrite fmap_gset_to_gmap //. } 

       iSplitL "Hmapa"; first by rewrite TMAP /auth_mapping_is /= map_fmap_singleton //.
       iSplit; first done.
       (* - intros ρ tid. rewrite MAP.  *)
       (*   rewrite lookup_gset_to_gmap_Some. *)
       (*   setoid_rewrite lookup_singleton_Some. split; naive_solver. *)

       (* - rewrite FUEL. rewrite dom_gset_to_gmap. set_solver. *)
       iPureIntro. set_solver. 
  }

  iSplitR.
  { iPureIntro. rewrite /tids_restrict.
    intros tid Hlocs. rewrite TMAP lookup_singleton_ne //.
    compute in Hlocs. set_solver. }    

  rewrite /LM_init_resource /has_fuels /=.
    
  (* iFrame. *)
  iSplitL "Hmodf".
  { by rewrite /frag_model_is. }
  iSplitL "Hfr".
  { rewrite /frag_free_roles_are. 
    iExists ∅. rewrite subseteq_empty_difference_L; set_solver. }

  rewrite !dom_gset_to_gmap. rewrite /frag_mapping_is. simpl.
  rewrite map_fmap_singleton. iFrame. 
  unfold frag_fuel_is.
  setoid_rewrite map_fmap_singleton. simpl.
  destruct (decide (live_roles M s1 = ∅)) as [-> | NE].
  { by iApply big_sepS_empty. }
  iDestruct (own_proper with "Hfuelf") as "Hfuelf".
  { apply auth_frag_proper. apply @gset_to_gmap_singletons. } 
  rewrite big_opS_auth_frag. rewrite big_opS_own; [| done].
  iApply (big_sepS_mono with "Hfuelf"). iIntros (ρ Hin) "H".
  iExists _. iFrame. iPureIntro. apply lookup_gset_to_gmap_Some. done.
Qed.


Global Instance LM_EM `{LM: LiveModel heap_lang M}: @ExecutionModel LM.
refine
  {|
    em_preGS := fun Σ => fairnessGpreS LM Σ;
    em_GS := fun Σ => fairnessGS LM Σ;
    em_Σ := fairnessΣ heap_lang M;
    em_Σ_subG := fun Σ => @subG_fairnessGpreS _ _ _ LM _ _;

    (* em_valid_evolution_step := valid_evolution_step (LM := LM); *)
    em_thread_post Σ := fun {_: fairnessGS LM Σ} (tid: locale heap_lang) => 
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
2: { intros ? fG. exact (em_lm_msi (LM := LM) (fairnessGS0 := fG)). } 
intros. iIntros. iMod (init_fairnessGS_LM _ s1 σ) as "[% [? X]]"; [done| ]. 
iModIntro. iExists _. iFrame. 
Defined. 

(* TODO: get rid of it*)
Global Instance LM_EM_fairPre `{LM: LiveModel heap_lang M}
                `{hGS: @heapGpreS Σ LM (@LM_EM _ LM)}:
  fairnessGpreS LM Σ.
Proof. apply hGS. Defined. 

(* TODO: get rid of it*)
Global Instance LM_EM_fair `{LM: LiveModel heap_lang M}
                `{hGS: @heapGS Σ LM (@LM_EM _ LM)}:
  fairnessGS LM Σ.
Proof. apply hGS. Defined.

Lemma tids_smaller_restrict_mapping `{M: FairModel}

  (c1 c2: cfg heap_lang) δ1 δ2 (ζ: locale heap_lang)
  (Hζs : tids_smaller c1.1 δ1)
  (DOM12: ls_mapping δ2 ⊆ ls_mapping δ1)
  (STEP: locale_step c1 (Some ζ) c2)
  :
  tids_smaller c2.1 δ2 (M := M).
Proof.
  unfold tids_smaller; simpl.
  intros ρ ζ0 Hin.
  destruct c1, c2.
  eapply from_locale_step =>//.
  rewrite /tids_smaller /= in Hζs. eapply Hζs.
  eapply lookup_weaken; eauto. 
Qed.

Lemma tids_dom_restrict_mapping `{LM: LiveModel heap_lang M} 
  (c1 c2: cfg heap_lang)
  (tmap1 tmap2: gmap (locale heap_lang) (gset (fmrole M))) (ζ: locale heap_lang)
  (Hstep : locale_step c1 (Some ζ) c2)
  (Hlocssmall: tids_restrict c1 tmap1)
  (TMAP2: exists S, tmap2 = <[ζ:=S]> (tmap1))
  :
  tids_restrict c2 tmap2.
Proof.
  intros ζ0 Hnotin.
  destruct TMAP2 as [? ->]. 
  destruct c1, c2. simpl in *. 
  apply lookup_insert_None; split.
  + apply Hlocssmall.
    have Hle := locales_of_list_step_incl _ _ _ _ _ Hstep. simpl.
    clear -Hnotin Hle. set_solver.
  + intros <-. 
    have ? := locales_of_list_step_incl _ _ _ _ _ Hstep. simpl.
    (* clear Hfueldom Hsamedoms. *)
    inversion Hstep. simplify_eq.
    assert (locale_of t1 e1 ∈ locales_of_list (t1 ++ e1 :: t2));
      last by eauto.
    apply locales_of_list_from_locale_from.
    rewrite from_locale_from_Some //. 
    eapply prefixes_from_spec.
    eexists _,_. by list_simplifier.
Qed.
  (* TODO: ?? *)
    (* - rewrite Hnewdom /new_dom. apply elem_of_equiv_empty_L. intros ρ [Hin1 Hin2]%elem_of_intersection. *)
    (*   assert (ρ ∈ dom (ls_fuel δ1)) *)
    (*     by set_solver -Hnewdom Hsamedoms Hfueldom. *)
    (*   set_solver -Hnewdom Hsamedoms Hfueldom. } *) 
