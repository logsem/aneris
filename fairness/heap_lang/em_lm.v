From trillium.fairness Require Export fairness resources fair_termination fuel fuel_ext. 
From trillium.fairness.heap_lang Require Export lang heap_lang_defs.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Export partial_ownership.


Definition LM_init_resource `{LM:LiveModel (locale heap_lang) M} `{!fairnessGS LM Σ}
   (s1: LM)
  (* FR *)
  : iProp Σ :=
  frag_model_is s1 ∗
  (∃ FR, frag_free_roles_are (FR ∖ live_roles _ s1)) ∗
  has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1))
  (PMPP := ActualOwnershipPartialPre). 

Definition init_thread_post `{LM:LiveModel (locale heap_lang) M} `{!fairnessGS LM Σ}
  (tid: locale heap_lang): iProp Σ :=
  (* tid ↦M ∅. *)
  frag_mapping_is {[ tid := ∅ ]}.

Definition lm_model_init `{LM: LiveModel (locale heap_lang) M} (δ: mstate LM) :=
  ls_fuel δ = gset_to_gmap (lm_fl LM δ) (live_roles _ (ls_under δ)) /\
  (* ls_mapping δ = gset_to_gmap 0%nat (live_roles _ (ls_under δ)).  *)
  ls_tmap δ (LM := LM) = {[ 0%nat := live_roles _ (ls_under δ) ]}. 

Definition lm_cfg_init (σ: cfg heap_lang) :=
  exists (e: expr), σ.1 = [e].

Definition lm_is_init_st `{LM: LiveModel (locale heap_lang) M} σ s := 
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

Lemma tids_restrict_smaller `{LM:LiveModel (locale heap_lang) M} (σ: cfg heap_lang) (δ: lm_ls LM):
  tids_restrict σ (ls_tmap δ) -> tids_smaller σ.1 δ.
Proof.
  rewrite /tids_smaller /tids_restrict. 
  intros. apply locales_of_list_from_locale_from'.
  destruct (decide (ζ ∈ locales_of_list σ.1)); [done| ].
  specialize (H _ n).
  eapply (ls_mapping_tmap_corr (LM := LM)) in H0 as [R [? ?]].
  congruence. 
Qed. 

Definition em_lm_msi `{LM:LiveModel (locale heap_lang) M} `{!fairnessGS LM Σ}
  (c: cfg heap_lang) (δ: mstate LM): iProp Σ :=
  model_state_interp δ ∗ ⌜ tids_restrict c (ls_tmap δ (LM := LM)) ⌝. 

(* TODO: how to make 'heap..' instantiations less wordy? *)
(* TODO: how to avoid different instances of EqDec and Cnt? *)
Lemma init_fairnessGS_LM Σ `{hPre: @fairnessGpreS (locale heap_lang) M LM Σ
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
       compute in Hlocs. set_solver. }

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


Global Instance LM_EM `{LM: LiveModel (locale heap_lang) M}: @ExecutionModel heap_lang LM.
refine
  {|
    em_preGS := fun Σ => fairnessGpreS LM Σ;
    em_GS := fun Σ => fairnessGS LM Σ;
    em_Σ := fairnessΣ (locale heap_lang) M;
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
Global Instance LM_EM_fairPre `{LM: LiveModel (locale heap_lang) M}
                `{hGS: @heapGpreS Σ LM (@LM_EM _ LM)}:
  fairnessGpreS LM Σ.
Proof. apply hGS. Defined. 

(* TODO: get rid of it*)
Global Instance LM_EM_fair `{LM: LiveModel (locale heap_lang) M}
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

Lemma tids_dom_restrict_mapping `{LM: LiveModel (locale heap_lang) M} 
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


Lemma tids_smaller_fork_step `{LM: LiveModel (locale heap_lang) M}  σ1 σ2 δ1 δ2 ζ τ_new
  (Hstep: locale_step σ1 (Some ζ) σ2)
  (SM: tids_smaller σ1.1 δ1)
  (MAP2: exists (R2: gset (fmrole M)), ls_mapping δ2 = map_imap
                                                    (λ (ρ : fmrole M) (o : locale heap_lang),
                                                      if decide (ρ ∈ R2) then Some τ_new else Some o)
                                                    (ls_mapping δ1))
  (FORK: ∃ tp1' efork, τ_new = locale_of σ1.1 efork /\ σ2.1 = tp1' ++ [efork] ∧ length tp1' = length σ1.1)
  :
  tids_smaller σ2.1 δ2 (M := M).
Proof.
  destruct σ1 as [tp1 σ1], σ2 as [tp2 σ2]. simpl in *.
  intros ρ ζ'.
  simpl in *. destruct MAP2 as [R2 ->].
  simpl. rewrite map_lookup_imap.
  destruct (ls_mapping δ1 !!ρ) eqn:Heq.
  2: { intros. simpl in *. discriminate. }
  
  destruct (decide (ρ ∈ R2)); first  (intros ?; simplify_eq).
  - destruct FORK as (tp1' & efork & (-> & -> & Hlen)).
    inversion Hstep as [? ? e1 ? e2 ? efs t1 t2 Hf1 YY Hprimstep |]. simplify_eq.
    assert (efs = [efork]) as ->.
    { symmetry. assert (length tp1' = length (t1 ++ e2 :: t2)).
      rewrite app_length //=; rewrite app_length //= in Hlen.
      clear Hlen. eapply app_inj_1 =>//. by list_simplifier. }
    inversion H.
    subst ζ'. 
    assert (is_Some (from_locale (t1 ++ e1 :: t2 ++ [efork]) (locale_of (t1 ++ e1 :: t2) efork))).
    + unfold from_locale. erewrite from_locale_from_Some; eauto.
      apply prefixes_from_spec. list_simplifier. eexists _, []. split=>//.
      by list_simplifier.
    + eapply from_locale_from_equiv =>//; [constructor |].
      (* rewrite H0. *)
      replace (t1 ++ e1 :: t2 ++ [efork]) with ((t1 ++ e1 :: t2) ++ [efork]);
        last by list_simplifier.
      replace (t1 ++ e2 :: t2 ++ [efork]) with ((t1 ++ e2 :: t2) ++ [efork]);
        last by list_simplifier.
      assert (locales_equiv (t1 ++ e1 :: t2) (t1 ++ e2 :: t2)).
      { apply locales_equiv_middle. eapply locale_step_preserve =>//. }
      assert (tp1' = t1 ++ e2 :: t2).
      { rewrite app_comm_cons in YY. 
        erewrite app_assoc in YY. eapply app_inj_tail in YY. apply YY. }
      apply locales_equiv_from_app =>//.
      * congruence.
      * eapply locales_equiv_from_refl. by list_simplifier. 
  - intros ?; simplify_eq.
    assert (is_Some (from_locale tp1 ζ')). 
    2: by eapply from_locale_step =>//.
    inversion H. subst. eauto. 
Qed.

Lemma tids_dom_fork_step `{LM: LiveModel (locale heap_lang) M}
  (c1 c2: cfg heap_lang) (ζ: locale heap_lang)
  (tmap1 tmap2: gmap (locale heap_lang) (gset (fmrole M)))
  τ_new (R1 R2: gset (fmrole M))
  (Hstep: locale_step c1 (Some ζ) c2)
  (Hsmall: ∀ ζ : locale heap_lang,
      ζ ∉ locales_of_list c1.1 → tmap1 !! ζ = None)
  (Hmapping : ζ ∈ dom tmap1)
  (FORK: (∃ tp1' efork, τ_new = locale_of c1.1 efork /\ c2.1 = tp1' ++ [efork] ∧ length tp1' = length c1.1))
  (TMAP2: tmap2 = <[τ_new:=R2]> (<[ζ:=R1]> (tmap1)))
  :
  ∀ ζ0 : locale heap_lang,
    ζ0 ∉ locales_of_list c2.1 → tmap2 !! ζ0 = None.
Proof.
  assert (Hlocincl: locales_of_list c1.1 ⊆ locales_of_list c2.1).
  { destruct c1 as [tp1 σ1], c2 as [tp2 σ2]. simpl in *.
    apply (locales_of_list_step_incl _ _ _ _ _ Hstep). }
  intros ζ' Hζ'.
  rewrite TMAP2.
  destruct c1 as [tp1 σ1], c2 as [tp2 σ2]. simpl in *.
  rewrite lookup_insert_ne.
  { rewrite lookup_insert_ne; last first.
    { intros <-.
      apply elem_of_dom in Hmapping as [? MM]. 
      rewrite Hsmall in MM; [congruence | naive_solver]. }
    apply Hsmall; set_unfold; naive_solver. }
  pose proof (locales_of_list_step_incl _ _ _ _ _ Hstep).
  (* clear Hfueldom Hsamedoms. *)
  assert (ζ' ∉ locales_of_list tp1) by eauto.
  intros contra. simplify_eq.
  destruct FORK as (tp1' & efork & (-> & -> & Hlen)).
  inversion Hstep as [? ? e1 ? e2 ? efs t1 t2 Hf1 YY Hprimstep |].
  simplify_eq.
  assert (efs = [efork]) as ->.
  { symmetry. assert (length tp1' = length (t1 ++ e2 :: t2)).
    rewrite app_length //=; rewrite app_length //= in Hlen.
    clear Hlen. eapply app_inj_1 =>//. by list_simplifier. }
  (* rewrite H0 in Hζ'. *)
  apply Hζ'. apply elem_of_list_fmap.
  eexists (t1 ++ e2 :: t2, _); split =>//.
  - erewrite locale_equiv =>//. apply locales_equiv_middle.
    eapply locale_step_preserve => //.
  - replace (t1 ++ e2 :: t2 ++ [efork]) with ((t1 ++ e2 :: t2) ++ [efork]); last by list_simplifier.
    rewrite prefixes_from_app.
    rewrite app_comm_cons app_assoc in YY. eapply app_inj_tail in YY.
    set_unfold; naive_solver.
Qed.


Lemma tids_smaller_model_step `{LM: LiveModel (locale heap_lang) M} c1 c2 ζ δ1 δ2
  (Hstep: locale_step c1 (Some ζ) c2)
  (Hless: tids_smaller c1.1 δ1)
  (* S is a subset of dom (ls_fuel δ1); *)
  (*      missing roles are those that are dropped by ζ; *)
  (*      new roles get assigned here *)
  (MAP2: exists f (S: gset (fmrole M)),
      ls_mapping δ2 = map_imap
                        (λ (ρ' : fmrole M) (_ : nat),
                          if decide (ρ' ∈ dom (ls_fuel δ1))
                          then ls_mapping δ1 !! ρ'
                          else Some ζ)
                        (gset_to_gmap f S)
  )
  :
  tids_smaller c2.1 δ2 (M := M).
Proof.  
  (* eapply tids_smaller_restrict_mapping; eauto. *)
  (* destruct MAP2 as (?&?&->).   *)
  unfold tids_smaller; simpl.
  simpl in MAP2. destruct MAP2 as (?&S&->).
  intros ρ' ? Hmim.
  rewrite map_lookup_imap in Hmim. rewrite lookup_gset_to_gmap in Hmim.
  destruct (decide (ρ' ∈ S)); last by rewrite option_guard_False in Hmim.
  rewrite option_guard_True //= in Hmim.
  destruct (decide (ρ' ∈ dom (ls_fuel δ1))). 
  + inversion Hstep; simplify_eq.
    eapply from_locale_step =>//. eapply Hless. rewrite -Hmim decide_True; auto. 
  + simplify_eq.
    inversion Hstep; simplify_eq.
    eapply from_locale_step =>//. unfold from_locale.
    simpl. rewrite decide_False in Hmim; [| done]. inversion Hmim. subst ζ0.  
    rewrite from_locale_from_Some; [done| ]. 
    apply prefixes_from_spec. exists t1, t2. by list_simplifier.
Qed.

Ltac by_contradiction :=
  match goal with
  | |- ?goal => destruct_decide (decide (goal)); first done; exfalso
  end.

Lemma mim_helper_model_step `{LM: LiveModel (locale heap_lang) M}
  (s2 : M)
  (fs1 fs2 : gmap (fmrole M) nat)
  (ρ : fmrole M)
  (δ1 : LM)
  (ζ : locale heap_lang)
  (fr1 : gset (fmrole M))
  (Hfr_new : live_roles M s2 ∖ live_roles M δ1 ⊆ fr1)
  (Hfuelsval : valid_new_fuelmap fs1 fs2 δ1 s2 ρ (LM := LM))
  (Hxdom : ∀ ρ : fmrole M, ls_mapping δ1 !! ρ = Some ζ ↔ ρ ∈ dom fs1)
  (HFR : fr1 ∩ dom (ls_fuel δ1) = ∅):
  maps_inverse_match
    (map_imap
       (λ (ρ' : fmrole M) (_ : nat),
          if decide (ρ' ∈ dom (ls_fuel δ1)) then ls_mapping δ1 !! ρ' else Some ζ)
       (gset_to_gmap 333 ((dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))))
    (<[ζ:=dom fs2]> (ls_tmap δ1 (LM := LM))).
Proof. 
  intros ρ' ζ'. simpl. rewrite map_lookup_imap.
  rewrite lookup_gset_to_gmap //=.
  destruct (decide (ρ' ∈ (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hin|Hnotin].
  - rewrite option_guard_True //=. destruct (decide (ρ' ∈ dom (ls_fuel δ1))).
    + destruct (decide (ζ' = ζ)) as [->|Hneq].
      * rewrite lookup_insert. split.
        { eexists; split =>//. apply elem_of_difference in Hin as [? Hin].
          apply not_elem_of_difference in Hin as [?|?]; [|done].
          rewrite decide_True in H; [set_solver| ]. done. }
        { intros (?&?&?). simplify_eq.
          rewrite decide_True; [| set_solver]. 
          apply Hxdom.
          destruct Hfuelsval as (?&?&?&?&?). by_contradiction.
          assert (ρ' ∈ live_roles M s2 ∖ live_roles M δ1).
          { set_solver. }
          assert (ρ' ∈ fr1).
          { set_solver. }
          assert (ρ' ∉ dom $ ls_fuel δ1) by set_solver.
          done. }
      * rewrite lookup_insert_ne //. rewrite decide_True; [| done]. 
        apply ls_mapping_tmap_corr.
    + split.
      * rewrite decide_False; [| done]. 
        intros Htid. simplify_eq.
        rewrite lookup_insert. eexists; split=>//.
        set_solver.
      * rewrite decide_False; [| done]. 
        assert (ρ' ∈ dom fs2) by set_solver. intros Hm. by_contradiction.
        rewrite lookup_insert_ne in Hm; last congruence.
        apply ls_mapping_tmap_corr in Hm.
        apply elem_of_dom_2 in Hm. rewrite ls_same_doms // in Hm.
  - destruct Hfuelsval as (?&?&?&?&Hinf&?). rewrite option_guard_False //=. split; first done.
    destruct (decide (ζ' = ζ)) as [->|Hneq].
    { rewrite lookup_insert //. intros (?&?&?). simplify_eq. set_solver. }
    rewrite lookup_insert_ne //.
    intros Habs%ls_mapping_tmap_corr.
    
    apply not_elem_of_difference in Hnotin as [Hnin|Hin].
    + apply elem_of_dom_2 in Habs. rewrite ls_same_doms in Habs. set_solver.
    + apply elem_of_difference in Hin as [Hin Hnin].
      apply Hxdom in Hin. rewrite Hin in Habs. congruence.  
Qed.       
