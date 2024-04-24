From trillium.fairness Require Import fuel lm_fair.


Section aux_trace_lang.
  Context `{Countable (locale Λ)}.
  Context `{LM: LiveModel (locale Λ) M LSI}.

  Notation "'Tid'" := (locale Λ). 

  Definition tids_smaller (c : list (expr Λ)) (δ: LiveState Tid M LSI) :=
    ∀ ρ ζ, (ls_mapping δ) !! ρ = Some ζ -> is_Some (from_locale c ζ).

  Definition tids_smaller_alt (c : list (expr Λ)) (δ: LiveState Tid M LSI) :=
    ∀ ζ, default ∅ (ls_tmap δ !! ζ) ≠ ∅ -> is_Some (from_locale c ζ).

  Lemma tids_smaller_defs_equiv (c : list (expr Λ)) (δ: LiveState Tid M LSI):
    tids_smaller c δ <-> tids_smaller_alt c δ.
  Proof.
    rewrite /tids_smaller /tids_smaller_alt. 
    split; intros SM.
    - intros τ NE. destruct (ls_tmap δ !! τ) eqn:TM; [| done].
      simpl in NE. apply gset_not_elem_of_equiv_not_empty_L in NE as [ρ IN]. 
      eapply (SM ρ). apply ls_mapping_tmap_corr. eauto.
    - intros ρ τ MAP. apply SM.
      apply ls_mapping_tmap_corr in MAP as (?&TM&?). rewrite TM. set_solver.
  Qed. 

  Definition tids_smaller' (c : list (expr Λ)) (δ: LiveState Tid M LSI) :=
    (* ∀ ρ ζ, (ls_mapping δ) !! ρ = Some ζ -> is_Some (from_locale c ζ). *)
    forall ζ, ζ ∈ dom (ls_tmap δ) -> is_Some (from_locale c ζ).

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
    intros RESTR ρ τ MAP. apply locales_of_list_from_locale_from'.
    destruct (decide (τ ∈ locales_of_list σ.1)); [done| ].
    specialize (RESTR _ n).
    eapply (ls_mapping_tmap_corr) in MAP as [R [? ?]].
    congruence. 
  Qed.
  
  (* TODO: get rid of one of these definitions *)
  Lemma tids_restrict_smaller' (σ: cfg Λ) (δ: lm_ls LM):
    tids_restrict σ (ls_tmap δ) -> tids_smaller' σ.1 δ.
  Proof.
    rewrite /tids_smaller' /tids_restrict. 
    intros RESTR τ MAP. apply locales_of_list_from_locale_from'.
    destruct (decide (τ ∈ locales_of_list σ.1)); [done| ].
    specialize (RESTR _ n).
    apply elem_of_dom in MAP as [? ?]. congruence. 
  Qed.

  Lemma tids_smaller'_restrict (σ: cfg Λ) (δ: lm_ls LM):
    tids_smaller' σ.1 δ -> tids_restrict σ (ls_tmap δ).
  Proof.
    rewrite /tids_smaller' /tids_restrict. 
    intros RESTR τ NIN. destruct (ls_tmap δ !! τ) eqn:T; [| done].
    specialize (RESTR _ (ltac:(apply elem_of_dom; done))).
    by apply locales_of_list_from_locale_from in RESTR. 
  Qed.
  
  Lemma tids_smaller'_stronger (c : list (expr Λ)) (δ: LiveState Tid M LSI):
    tids_smaller' c δ -> tids_smaller c δ.
  Proof. 
    intros TS. red. intros. apply TS.
    eapply mim_in_1; eauto. 
    apply ls_mapping_tmap_corr.
  Qed. 

  Lemma tids_smaller_restrict_mapping
    (c1 c2: cfg Λ) δ1 δ2 (ζ: locale Λ)
    (Hζs : tids_smaller c1.1 δ1)
    (DOM12: ls_mapping δ2 ⊆ ls_mapping δ1 (LSI := LSI))
    (STEP: locale_step c1 (Some ζ) c2)
    :
    tids_smaller c2.1 δ2.
  Proof.
    unfold tids_smaller; simpl.
    intros ρ ζ0 Hin.
    destruct c1, c2.
    eapply from_locale_step =>//.
    rewrite /tids_smaller /= in Hζs. eapply Hζs.
    eapply lookup_weaken; eauto. 
  Qed.

  Lemma tids_smaller_fuel_step
    (ζ : locale Λ) (fs: gmap (fmrole M) nat) (σ: cfg Λ) (δ: lm_ls LM) c2
    (NE  : dom fs ≠ ∅)
    (STEP : locale_step σ (Some ζ) c2)
    (TR : tids_smaller σ.1 δ )
    (Hxdom : ∀ ρ, ls_mapping δ !! ρ = Some ζ ↔ ρ ∈ dom (S <$> fs))
    δ2
    (STEPM : lm_ls_trans LM δ (Silent_step ζ) δ2)
    (TMAP' : ls_tmap δ2 = <[ζ:=dom fs ∖ ∅]> (ls_tmap δ)):
    tids_smaller c2.1 δ2.
  Proof.
    eapply tids_smaller_restrict_mapping; eauto.
    setoid_rewrite dom_fmap in Hxdom. eapply mim_lookup_helper in Hxdom; eauto.
    2: by apply ls_mapping_tmap_corr.
    eapply maps_inverse_match_subseteq.
    1, 2: by apply ls_mapping_tmap_corr.
    { rewrite TMAP'. apply elem_of_dom_2 in Hxdom. set_solver. }
    intros ??? TM1 TM2.
    rewrite TMAP' in TM1. eapply lookup_insert_Some in TM1.
    set_solver. 
  Qed.
  
  
  Lemma tids_dom_restrict_mapping `{EqDecision (expr Λ)}
    (c1 c2: cfg Λ)
    (tmap1 tmap2: gmap (locale Λ) (gset (fmrole M))) (ζ: locale Λ)
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
      eapply prefixes_from_spec; eauto. 
  Qed.


  Lemma tids_smaller_fork_step `{EqDecision (expr Λ)} 
    σ1 σ2 δ1 δ2 ζ τ_new
    (Hstep: locale_step σ1 (Some ζ) σ2)
    (SM: tids_smaller σ1.1 δ1)
    (MAP2: exists (R2: gset (fmrole M)), ls_mapping δ2 = map_imap
                                                      (λ (ρ : fmrole M) (o : locale Λ),
                                                        if decide (ρ ∈ R2) then Some τ_new else Some o)
                                                      (ls_mapping δ1 (LSI := LSI)))
    (FORK: ∃ tp1' efork, τ_new = locale_of σ1.1 efork /\ σ2.1 = tp1' ++ [efork] ∧ length tp1' = length σ1.1)
    :
    tids_smaller σ2.1 δ2.
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
      inversion H0.
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
        { rewrite app_comm_cons in H1. 
          erewrite app_assoc in H1. eapply app_inj_tail in H1. apply H1. }
        apply locales_equiv_from_app =>//.
        * congruence.
        * eapply locales_equiv_from_refl. by list_simplifier. 
    - intros ?; simplify_eq.
      assert (is_Some (from_locale tp1 ζ')). 
      2: by eapply from_locale_step =>//.
      inversion H0. subst. eauto. 
  Qed.
  
  Lemma tids_dom_fork_step
    (c1 c2: cfg Λ) (ζ: locale Λ)
    (tmap1 tmap2: gmap (locale Λ) (gset (fmrole M)))
    τ_new (R1 R2: gset (fmrole M))
    (Hstep: locale_step c1 (Some ζ) c2)
    (Hsmall: ∀ ζ : locale Λ, ζ ∉ locales_of_list c1.1 → tmap1 !! ζ = None)
    (Hmapping : ζ ∈ dom tmap1)
    (FORK: (∃ tp1' efork, τ_new = locale_of c1.1 efork /\ c2.1 = tp1' ++ [efork] ∧ length tp1' = length c1.1))
    (TMAP2: tmap2 = <[τ_new:=R2]> (<[ζ:=R1]> (tmap1)))
    :
    ∀ ζ0 : locale Λ,
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
      rewrite app_comm_cons app_assoc in H2. eapply app_inj_tail in H2.
      set_unfold; naive_solver.
  Qed.
  
  Lemma tids_smaller_model_step `{EqDecision (expr Λ)}
    c1 c2 ζ δ1 δ2
    (Hstep: locale_step c1 (Some ζ) c2)
    (Hless: tids_smaller c1.1 δ1)
    (* S is a subset of dom (ls_fuel δ1); *)
    (*      missing roles are those that are dropped by ζ; *)
    (*      new roles get assigned here *)
    (MAP2: exists f (S: gset (fmrole M)),
        ls_mapping δ2 = map_imap
                          (λ (ρ' : fmrole M) (_ : nat),
                            if decide (ρ' ∈ dom (ls_fuel δ1))
                            then ls_mapping δ1 (LSI := LSI) !! ρ'
                            else Some ζ)
                          (gset_to_gmap f S)
    )
    :
    tids_smaller c2.1 δ2.
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
      eapply from_locale_step =>//. eapply Hless.
      rewrite -Hmim. eauto. 
    + simplify_eq.
      inversion Hstep; simplify_eq.
      eapply from_locale_step =>//. unfold from_locale.
      simpl.
      rewrite from_locale_from_Some; [done| ]. 
      eapply prefixes_from_spec. exists t1, t2. by list_simplifier.
  Qed.


  Lemma tids_smaller'_restrict_mapping
    (c1 c2: cfg Λ) (δ1 δ2: LiveState (locale Λ) M LSI) (ζ: locale Λ)
    (Hζs : tids_smaller' c1.1 δ1)
    (DOM12: dom (ls_tmap δ2) ⊆ dom (ls_tmap δ1))
    (STEP: locale_step c1 (Some ζ) c2)
    :
    tids_smaller' c2.1 δ2.
  Proof.
    unfold tids_smaller'; simpl.
    intros ζ0 Hin.
    destruct c1, c2.
    eapply from_locale_step =>//.
    rewrite /tids_smaller' /= in Hζs. eapply Hζs.
    intuition. 
  Qed.
  
  Lemma tids_smaller'_model_step c1 c2 ζ
    (δ1 δ2: LiveState (locale Λ) M LSI)
    (Hstep: locale_step c1 (Some ζ) c2)
    (Hless: tids_smaller' c1.1 δ1)
    (IN: ζ ∈ dom (ls_tmap δ1))
    (MAP2: exists (fs2: gmap (fmrole M) nat), ls_tmap δ2 = <[ζ:=dom fs2]> (ls_tmap δ1))
    :
    tids_smaller' c2.1 δ2.
  Proof. 
    unfold tids_smaller'; simpl.
    simpl in MAP2. destruct MAP2 as (?&->).
    intros ζ0 [? Hmim]%elem_of_dom.
    rewrite lookup_insert_Some in Hmim. 
    destruct c1, c2. simpl in *. 
    destruct Hmim as [[<- <-]|[? TM]].
    + eapply from_locale_step =>//; eauto.
    + eapply from_locale_step =>//.
      eapply Hless. by apply elem_of_dom.
  Qed. 
  
  (* TODO: refactor proof *)
  Lemma tids_smaller'_fork_step `{EqDecision (expr Λ)}
    σ1 σ2 (δ1 δ2: lm_ls LM) ζ τ_new
    (Hstep: locale_step σ1 (Some ζ) σ2)
    (SM: tids_smaller' σ1.1 δ1)
    (DOM: ζ ∈ dom (ls_tmap δ1))
    (MAP2: exists R2 R1, ls_tmap δ2 = <[τ_new:=R2]> (<[ζ:=R1]> (ls_tmap δ1)))
    (FORK: ∃ tp1' efork, τ_new = locale_of σ1.1 efork /\ σ2.1 = tp1' ++ [efork] ∧ length tp1' = length σ1.1)
    :
    tids_smaller' σ2.1 δ2.
  Proof.
    destruct σ1 as [tp1 σ1], σ2 as [tp2 σ2]. simpl in *.
    red. intros ζ0 [Rζ0 IN2]%elem_of_dom.
    simpl in *.
    destruct MAP2 as (R2 & R1 & MAP2).
    simpl. rewrite MAP2 in IN2.
    repeat rewrite lookup_insert_Some in IN2.
    destruct IN2 as [[<- <-] | ].
    {
      destruct FORK as (tp1' & efork & (-> & -> & Hlen)).
      inversion Hstep as [? ? e1 ? e2 ? efs t1 t2 Hf1 YY Hprimstep |]. simplify_eq.
      assert (efs = [efork]) as ->.
      { symmetry. assert (length tp1' = length (t1 ++ e2 :: t2)).
        rewrite app_length //=; rewrite app_length //= in Hlen.
        clear Hlen. eapply app_inj_1 =>//. by list_simplifier. }
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
      { rewrite app_comm_cons in H0.
        erewrite app_assoc in H0. eapply app_inj_tail in H0. apply H0. }
      apply locales_equiv_from_app =>//.
      * congruence.
      * eapply locales_equiv_from_refl. by list_simplifier. }
  
    destruct H0 as [NEQ [[<- <-]| ?]].
    { assert (is_Some (from_locale tp1 ζ)).
      2: by eapply from_locale_step =>//.
      by apply SM. }
    
    destruct H0 as [? ?].
    rename ζ into ζ_step, ζ0 into ζ, τ_new into ζ_new, Rζ0 into Rζ. 
    rename NEQ into NOTNEW. rename H0 into NOTSTEP. rename H1 into TMζ1. 
    (* can also assume: ls_tmap δ1 !! ζ_step = Some (R1 ∪ R2) *)
    
    assert (ls_tmap δ2 !! ζ = Some Rζ) as TMζ2.
    { rewrite -TMζ1 MAP2. repeat rewrite lookup_insert_ne; auto. }
    
    edestruct (SM ζ) as [eζ FLζ1].
    { eapply elem_of_dom. eauto. }
    destruct FORK as (tp1' & efork & (-> & -> & Hlen)).
    
    inversion Hstep as [? ? e1 ? e2 ? efs t1 t2 Hf1 YY Hprimstep |]. simplify_eq.
    assert (efs = [efork]) as ->.
    {      
      symmetry. assert (length tp1' = length (t1 ++ e2 :: t2)).
      { 
        rewrite app_length //=. rewrite app_length //= in Hlen. }
      clear Hlen. eapply app_inj_1 =>//. by list_simplifier. }
    assert (tp1' = t1 ++ e2 :: t2).
    { rewrite app_comm_cons in H0.
      erewrite app_assoc in H0.
      eapply app_inj_tail in H0. apply H0. }
    subst tp1'.
    assert (locales_equiv (t1 ++ e1 :: t2) (t1 ++ e2 :: t2)) as EQUIV. 
    { apply locales_equiv_middle. eapply locale_step_preserve =>//. }
    eapply from_locale_from_equiv.
    { eapply locales_equiv_from_refl. done. }
    { apply locales_equiv_from_app.
      { apply EQUIV. }
      eapply locales_equiv_from_refl. by list_simplifier. }
    exists eζ. apply from_locale_from_Some_app. done. 
  Qed.

End aux_trace_lang.
