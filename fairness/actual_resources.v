From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel resources. 


Section actual_ownership.
  Context `{LM: LiveModel Λ M}.
  Context `{Countable (locale Λ)}.
  Context `{EqDecision (expr Λ)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  (* TODO: decide what to do with notations *)
  Notation "tid ↦M R" := (frag_mapping_is {[ tid := R ]}) (at level 33).
  Notation "tid ↦m ρ" := (frag_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
  Notation "ρ ↦F f" := (frag_fuel_is {[ ρ := f ]}) (at level 33).

  Global Instance ActualOwnershipPartialPre:
    @PartialModelPredicatesPre _ _ _ Σ M. 
  Proof.
    refine {|
        partial_model_is := frag_model_is;
        partial_free_roles_are := frag_free_roles_are;
        partial_fuel_is := frag_fuel_is;
        partial_mapping_is := frag_mapping_is;
      |}.
    - intros. rewrite /frag_fuel_is.
      rewrite map_fmap_union. rewrite -gmap_disj_op_union.
      2: { by apply map_disjoint_fmap. }
      by rewrite auth_frag_op own_op.
    - intros. rewrite /frag_free_roles_are.
      rewrite -gset_disj_union; auto.  
      by rewrite auth_frag_op own_op.
    - iApply empty_frag_free_roles. 
  Defined. 

  Lemma has_fuel_in ζ δ fs n:
    has_fuels ζ fs -∗ model_state_interp n δ -∗ ⌜ ∀ ρ, ls_mapping δ !! ρ = Some ζ <-> ρ ∈ dom fs ⌝.
  Proof.
    unfold model_state_interp, has_fuels, auth_mapping_is, frag_mapping_is.
    iIntros "[Hζ Hfuels] (%m&%FR&Hafuel&Hamapping &HFR&%Hmapinv&Hamod&Hfr) %ρ".
    iCombine "Hamapping Hζ" as "H".
    iDestruct (own_valid with "H") as %Hval. iPureIntro.
    apply auth_both_valid_discrete in Hval as [Hval ?].
    rewrite map_fmap_singleton in Hval.
    apply singleton_included_exclusive_l in Hval =>//; last by typeclasses eauto.
    rewrite -> lookup_fmap, leibniz_equiv_iff in Hval.
    apply fmap_Some_1 in Hval as (R'&HMζ&?). simplify_eq.
    rewrite (Hmapinv ρ ζ) HMζ. split.
    - intros (?&?&?). by simplify_eq.
    - intros ?. eexists. split; eauto.
  Qed.

  Lemma has_fuel_fuel ζ δ fs n:
    has_fuels ζ fs -∗ model_state_interp n δ -∗ 
    ⌜ ∀ ρ, ρ ∈ dom fs -> ls_fuel δ !! ρ = fs !! ρ ⌝.
  Proof.
    unfold has_fuels, model_state_interp, auth_fuel_is.
    iIntros "[Hζ Hfuels] (%m&%FR&Hafuel&Hamapping&HFR&%Hmapinv&Hamod)" (ρ Hρ).
    iDestruct (big_sepS_delete _ _ ρ with "Hfuels") as "[(%f&%Hfs&Hfuel) _]" =>//.
    iCombine "Hafuel Hfuel" as "H".
    iDestruct (own_valid with "H") as %Hval. iPureIntro.
    apply auth_both_valid_discrete in Hval as [Hval ?].
    rewrite map_fmap_singleton in Hval.
    apply singleton_included_exclusive_l in Hval =>//; last by typeclasses eauto.
    rewrite -> lookup_fmap, leibniz_equiv_iff in Hval.
    apply fmap_Some_1 in Hval as (f'&Hfuelρ&?). simplify_eq.
    rewrite Hfuelρ Hfs //.
  Qed.

  Lemma frag_free_roles_fuels_disj: forall n δ fr fs tid,
        model_state_interp n δ -∗ frag_free_roles_are fr -∗ 
        has_fuels tid fs (PMPP := ActualOwnershipPartialPre) -∗
        ⌜ fr ## dom fs⌝. 
  Proof using. 
    iIntros (?????) "MSI FREE FUELS". 
    rewrite /model_state_interp.
    iAssert (⌜ dom fs ⊆ dom (ls_fuel δ) ⌝)%I as "%INCL2".
    { iDestruct (has_fuel_fuel with "FUELS MSI") as "%IN".
      iPureIntro. apply elem_of_subseteq.
      intros ? DOM. specialize (IN _ DOM).
      apply elem_of_dom. rewrite IN. by apply elem_of_dom.  }
    iDestruct "MSI" as (??) "(?&?&FREE'&?&?&?&%DISJ)".
    iDestruct (free_roles_inclusion with "FREE' FREE") as "%INCL1".
    iPureIntro. set_solver. 
  Qed.

  Definition fuel_apply (fs' F:  gmap (fmrole M) nat) (LR: gset (fmrole M)):
    gmap (fmrole M) nat :=
    map_imap
      (λ (ρ: fmrole M ) (fold : nat),
       match decide (ρ ∈ dom fs') with
       | left x => fs' !! ρ
       | right _ => F !! ρ
       end) (gset_to_gmap (0%nat) LR).

  Definition update_fuel_resource (δ1: LiveState Λ M) (fs1 fs2: gmap (fmrole M) nat) (s2: M):
    gmap (fmrole M) nat :=


    fuel_apply fs2 (δ1.(ls_fuel (Λ := Λ))) (((dom $ ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2)).

  Lemma elem_of_frame_excl_map
        (fs F: gmap (fmrole M) nat)
        (mf: gmap (fmrole M) (excl nat))
        (ρ: fmrole M)
        (f: excl nat):
    ✓ ((λ f : nat, Excl f) <$> F) ->
    ((λ f : nat, Excl f) <$> F ≡ ((Excl <$> fs) ⋅? (Some mf))) ->
    mf !! ρ = Some f ->
    ρ ∈ dom F ∖ dom fs.
  Proof.
    intros Hval Heq Hlk. simpl in Heq.
    specialize (Heq ρ). rewrite lookup_op Hlk !lookup_fmap in Heq.
    destruct (decide (ρ ∈ dom F)) as [HF|HF]; last first.
    { exfalso. apply not_elem_of_dom in HF. rewrite HF //= in Heq.
      destruct (fs !! ρ) eqn:Hfs; inversion Heq as [A S D G Habs|A Habs];
        setoid_rewrite -> Hfs in Habs; by compute in Habs. }
    destruct (decide (ρ ∈ dom fs)) as [Hfs|Hfs].
    { exfalso. apply elem_of_dom in Hfs as [f' Hlk'].
      rewrite Hlk' /= in Heq.
      suffices: Some f = None by eauto.
      eapply exclusive_Some_l; last first.
      - specialize (Hval ρ). rewrite -> lookup_fmap, Heq in Hval.
        apply Hval.
      - typeclasses eauto. }
    set_solver.
  Qed.

  Lemma update_fuel fs fs' F:
    let LR := (dom F ∪ dom fs') ∖ (dom fs ∖ dom fs') in
    (fs ≠ ∅) ->
    (dom fs' ∖ dom fs ∩ dom F = ∅) ->
    auth_fuel_is F -∗
    ([∗ map] ρ ↦ f ∈ fs, ρ ↦F f) ==∗
      auth_fuel_is (fuel_apply fs' F LR) ∗
      ([∗ map] ρ ↦ f ∈ fs', ρ ↦F f).
  Proof.
    iIntros (? Hnotemp Hdisj) "Hafuel Hfuel".
    rewrite {1}/frag_fuel_is -big_opM_own //.
    setoid_rewrite map_fmap_singleton.
    rewrite -big_opM_auth_frag.
    iCombine "Hafuel Hfuel" as "H".
    iMod (own_update with "H") as "[A B]"; last first.
    { iModIntro.
      destruct (decide (fs' = ∅)) as [Heq|]; last first.
      -  rewrite {1}/frag_fuel_is -big_opM_own //.
         iSplitL "A"; done.
      - rewrite Heq. iSplitL "A"; first done. done. }

    simpl.
    setoid_rewrite map_fmap_singleton.
    rewrite -big_opM_auth_frag.

    simpl.
    apply auth_update.

    apply local_update_discrete.

    intros mf Hval Heq.
    split.
    { intros ρ. rewrite /fuel_apply lookup_fmap map_lookup_imap.
      rewrite lookup_gset_to_gmap.
      destruct (decide (ρ ∈ LR)).
      - rewrite option_guard_True //=.
        destruct (decide (ρ ∈ dom fs')) as [Hd|Hd].
        + rewrite decide_True //=. apply elem_of_dom in Hd as [? Hsome].
          rewrite Hsome //.
        + rewrite decide_False //= -lookup_fmap. apply (Hval ρ).
      - rewrite option_guard_False //=. }

    intros ρ. rewrite /fuel_apply lookup_fmap map_lookup_imap.
    rewrite lookup_gset_to_gmap.
    rewrite -big_opM_fmap big_opM_singletons.
    rewrite <-big_opM_fmap in Heq. setoid_rewrite big_opM_singletons in Heq.
    destruct (decide (ρ ∈ LR)).
    - rewrite option_guard_True //=.
      destruct (decide (ρ ∈ dom fs')) as [Hd'|Hd'].
      + rewrite decide_True //=. apply elem_of_dom in Hd' as [? Hsome].
        rewrite Hsome //= lookup_opM.
        rewrite lookup_fmap Hsome.
        destruct mf as [mf|]; simpl; last done.
        destruct (mf !! ρ) as [f|] eqn:Hlk; rewrite Hlk //.

        assert (ρ ∈ dom F ∖ dom fs).
        { eauto using elem_of_frame_excl_map. }
        assert (ρ ∈ dom fs').
        { apply elem_of_dom. eauto. }
        set_solver.
      + rewrite decide_False //= -lookup_fmap.
        rewrite Heq.
        destruct (decide (ρ ∈ dom fs)) as [Hd|Hd];
          first set_solver.
        pose proof Hd as Hd2. pose proof Hd' as Hd'2.
        apply not_elem_of_dom in Hd2, Hd'2. rewrite !lookup_opM !lookup_fmap Hd2 Hd'2 //.
    - rewrite option_guard_False //=.
      rewrite lookup_opM lookup_fmap.
      destruct mf as [mf|]; simpl.
      + destruct (mf !! ρ) as [f|] eqn:Hlk; rewrite Hlk //.
        * assert (ρ ∈ dom F ∖ dom fs).
          { eauto using elem_of_frame_excl_map. }
          set_solver.
        * assert (Hnotin: ρ ∉ dom fs') by set_solver.
          apply not_elem_of_dom in Hnotin. rewrite Hnotin //.
      + assert (Hnotin: ρ ∉ dom fs') by set_solver.
        apply not_elem_of_dom in Hnotin. rewrite Hnotin //.
  Qed.

  Lemma update_mapping ζ (R' : gset $ fmrole M) (R: gset (fmrole M)) m :
    auth_mapping_is m -∗ ζ ↦M R ==∗ auth_mapping_is (<[ ζ := R' ]> m) ∗ ζ ↦M R'.
  Proof.
    iIntros "Hamap Hmap".
    iCombine "Hamap Hmap" as "H".
    iMod (own_update with "H") as "[A B]"; last first.
    { iModIntro. iSplitL "A"; iFrame. }
    rewrite !map_fmap_singleton fmap_insert.
    eapply auth_update, singleton_local_update_any.
    intros. by apply exclusive_local_update.
  Qed.

  Lemma mapping_lookup ζ m R:
    auth_mapping_is m -∗ ζ ↦M R -∗ ⌜ ζ ∈ dom m ⌝.
  Proof.
    unfold auth_mapping_is, frag_mapping_is.
    iIntros "Ham Hm".
    iCombine "Ham Hm" as "H".
    iDestruct (own_valid with "H") as %Hval. iPureIntro.
    apply auth_both_valid_discrete in Hval as [Hval ?].
    rewrite map_fmap_singleton in Hval.
    apply singleton_included_exclusive_l in Hval =>//; last by typeclasses eauto.
    rewrite -> lookup_fmap, leibniz_equiv_iff in Hval.
    apply fmap_Some_1 in Hval as (f'&Hfuelρ&?). simplify_eq.
    apply elem_of_dom. eauto.
  Qed.

  Lemma update_mapping_new_locale ζ ζ' (R R1 R2 : gset $ fmrole M) m :
    ζ' ∉ dom m ->
    auth_mapping_is m -∗
    ζ ↦M R ==∗
    auth_mapping_is (<[ ζ' := R2]> (<[ ζ := R1 ]> m)) ∗
    ζ ↦M R1 ∗ ζ' ↦M R2.
  Proof.
    iIntros (Hnotin) "Hamap Hmap".
    iDestruct (mapping_lookup with "Hamap Hmap") as %Hin.
    iCombine "Hamap Hmap" as "H".
    iMod (own_update (A := (authUR (gmapUR _ (exclR (gsetR (RoleO M)))))) _ _ (
                       ● ((λ f : gset (fmrole M), Excl f) <$> ((<[ ζ := R1 ]> m)))
                         ⋅ ◯ ((λ f : gset (fmrole M), Excl f) <$> {[ζ := R1]})
                     ) with "H") as "[A B]".
    { rewrite !map_fmap_singleton fmap_insert.
      eapply auth_update. eapply singleton_local_update_any.
      intros. by apply exclusive_local_update. }
    iCombine "A B" as "H".
    iMod (own_update (A := (authUR (gmapUR _ (exclR (gsetR (RoleO M)))))) _ _ (
                       ● ((λ f : gset (fmrole M), Excl f) <$> (<[ ζ' := R2]> (<[ ζ := R1 ]> m)))
                         ⋅ ◯ ((λ f : gset (fmrole M), Excl f) <$> {[ζ := R1 ; ζ' := R2]})
                     ) with "H") as "[A B]"; last first.
    { iModIntro. iSplitL "A"; first iFrame. rewrite !fmap_insert fmap_empty insert_empty.
      replace (◯ {[ζ := Excl R1; ζ' := Excl R2]}) with (◯ {[ζ := Excl R1]} ⋅ ◯ {[ζ' := Excl R2]}).
      - iDestruct "B" as "[A B]". iSplitL "A"; rewrite /frag_mapping_is map_fmap_singleton //.
      - rewrite -auth_frag_op insert_singleton_op //. rewrite lookup_singleton_ne //. set_solver. }
    rewrite !map_fmap_singleton fmap_insert !fmap_insert.
    rewrite (insert_commute _ _ _ (Excl R1) (Excl R2)); last set_solver.
    eapply auth_update. rewrite fmap_empty. eapply alloc_local_update; eauto.
    - rewrite lookup_insert_ne; last set_solver. apply not_elem_of_dom. set_solver.
    - done.
  Qed.

  Lemma update_mapping_delete ζ (Rrem : gset $ fmrole M) (R: gset (fmrole M)) m :
    auth_mapping_is m -∗ ζ ↦M R ==∗ auth_mapping_is (<[ ζ := R ∖ Rrem ]> m) ∗ ζ ↦M (R ∖ Rrem).
  Proof.
    eauto using update_mapping.
  Qed.

  Lemma update_mapping_add ζ (Radd : gset $ fmrole M) (R: gset (fmrole M)) m :
    auth_mapping_is m -∗ ζ ↦M R ==∗ auth_mapping_is (<[ ζ := R ∪ Radd ]> m) ∗ ζ ↦M (R ∪ Radd).
  Proof.
    eauto using update_mapping.
  Qed.


  Lemma update_has_fuels ζ fs fs' F m :
    let LR := (dom F ∪ dom fs') ∖ (dom fs ∖ dom fs') in
    (fs ≠ ∅) ->
    (dom fs' ∖ dom fs ∩ dom F = ∅) ->
    has_fuels ζ fs -∗
    auth_fuel_is F -∗
    auth_mapping_is m ==∗
    auth_fuel_is (fuel_apply fs' F LR) ∗
    has_fuels ζ fs' ∗
    auth_mapping_is (<[ ζ := dom fs' ]> m).
  Proof.
    iIntros (LR Hfs Hdom) "Hfuels Hafuels Hamapping".
    rewrite !has_fuels_equiv. iDestruct "Hfuels" as "[Hmapping Hfuels]".    
    iMod (update_fuel with "Hafuels Hfuels") as "[Hafuels Hfuels]" =>//.
    iMod (update_mapping with "Hamapping Hmapping") as "[Hamapping Hmapping]".
    iModIntro.
    iFrame.
  Qed.

  Lemma update_has_fuels_no_step ζ fs fs' F m :
    let LR := (dom F ∪ dom fs') ∖ (dom fs ∖ dom fs') in
    (fs ≠ ∅) ->
    (dom fs' ⊆ dom fs) ->
    has_fuels ζ fs -∗
    auth_fuel_is F -∗
    auth_mapping_is m ==∗
    auth_fuel_is (fuel_apply fs' F LR) ∗
    has_fuels ζ fs' ∗
    auth_mapping_is (<[ ζ := dom fs' ]> m).
  Proof.
    iIntros (LR Hfs Hdom) "Hfuels Hafuels Hamapping".
    rewrite !has_fuels_equiv. iDestruct "Hfuels" as "[Hmapping Hfuels]".
    iMod (update_fuel fs fs' with "Hafuels Hfuels") as "[Hafuels Hfuels]"; [done|set_solver|].
    iMod (update_mapping with "Hamapping Hmapping") as "[Hamapping Hmapping]".
    iModIntro. iFrame.
  Qed.

  Lemma update_has_fuels_no_step_no_change ζ fs fs' F m :
    let LR := (dom F ∪ dom fs') ∖ (dom fs ∖ dom fs') in
    (fs ≠ ∅) ->
    (dom fs' = dom fs) ->
    has_fuels ζ fs -∗
    auth_fuel_is F -∗
    auth_mapping_is m ==∗
    auth_fuel_is (fuel_apply fs' F LR) ∗
    has_fuels ζ fs' ∗
    auth_mapping_is m.
  Proof.
    iIntros (LR Hfs Hdom) "Hfuels Hafuels Hamapping".
    rewrite !has_fuels_equiv. iDestruct "Hfuels" as "[Hmapping Hfuels]".
    iMod (update_fuel fs fs' with "Hafuels Hfuels") as "[Hafuels Hfuels]" =>//.
    { rewrite Hdom. set_solver. }
    iModIntro.
    iFrame. rewrite Hdom //.
  Qed.


End actual_ownership. 

Section ActualOwnershipImpl.
  Context `{LM: LiveModel Λ M}.
  Context `{Countable (locale Λ)}.
  Context `{EqDecision (expr Λ)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  Lemma actual_update_no_step_enough_fuel
  (δ1: LM) rem c1 c2 fs ζ:
    (dom fs ≠ ∅) ->
    (live_roles _ δ1) ∩ rem = ∅ →
    rem ⊆ dom fs →
    locale_step c1 (Some ζ) c2 ->
    has_fuels_S ζ fs -∗ model_state_interp c1 δ1
    ==∗ ∃ δ2 (ℓ : mlabel LM),
        ⌜labels_match (LM:=LM) (Some ζ) ℓ
        ∧ valid_evolution_step (Some ζ) c2 δ1 ℓ δ2 (LM := LM)⌝ ∗
            has_fuels ζ (fs ⇂ (dom fs ∖ rem)) ∗ model_state_interp c2 δ2.
  Proof.
    iIntros "%HnotO %Holdroles %Hincl %Hstep Hf Hmod".
    destruct c2 as [tp2 σ2].
    destruct (set_choose_L _ HnotO) as [??].
    iDestruct (has_fuel_in with "Hf Hmod") as %Hxdom; eauto.
    iDestruct (has_fuel_fuel with "Hf Hmod") as "%Hfuel"; eauto.
    iDestruct (model_state_interp_tids_smaller with "Hmod") as %Hζs.
    iDestruct "Hmod" as "(%m & %FR & Hfuel & Hamapping & HFR & %Hminv & %Hlocssmall & Hmodel & %HFR)".
    unfold has_fuels_S.
    simpl in *.

    set new_dom := ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem).
    set new_mapping := ls_mapping δ1 ⇂ new_dom.

    assert (dom (fuel_apply (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs) (ls_fuel δ1)
                   ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem)) = new_dom) as Hnewdom.
    { rewrite /fuel_apply map_imap_dom_eq ?dom_gset_to_gmap //.
      intros ρ0 _ Hindom.
      case_decide as Hninf; [by apply elem_of_dom|].
      apply elem_of_difference in Hindom as [Hin1 ?].
      apply elem_of_union in Hin1 as [?|Hin2]; first by apply elem_of_dom.
      exfalso. apply Hninf. apply elem_of_dom in Hin2 as [f ?].
      eapply elem_of_dom_2. rewrite map_filter_lookup_Some. split =>//.
      apply elem_of_difference; split =>//. by eapply elem_of_dom_2. }

    assert (Hsamedoms: dom new_mapping =
                       dom (fuel_apply (fs ⇂ (dom fs ∖ rem))
                                       (ls_fuel δ1)
                                       ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem))).
    { rewrite /new_mapping /new_dom. unfold fuel_apply.
      assert (dom fs ⊆ dom δ1.(ls_fuel)) as Hdom_le.
      { intros ρ Hin. rewrite elem_of_dom Hfuel; last set_solver.
        apply elem_of_dom in Hin as [? Hin]. rewrite lookup_fmap Hin //=. }
      rewrite map_imap_dom_eq; last first.
      { intros ρ _ Hin. rewrite dom_gset_to_gmap in Hin.
        case_decide; [by apply elem_of_dom|].
        apply elem_of_dom. set_solver +Hin Hdom_le. }
      rewrite dom_domain_restrict ?dom_gset_to_gmap ?ls_same_doms //.
      set_solver +Hdom_le. }
    assert (Hfueldom: live_roles _ δ1 ⊆
     dom (fuel_apply (fs ⇂ (dom fs ∖ rem))
                     (ls_fuel δ1)
                     ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem))).
    { rewrite /fuel_apply Hnewdom.
      intros ρ Hin. apply elem_of_difference; split;
        [apply ls_fuel_dom in Hin; set_solver +Hin|
          set_solver -Hlocssmall Hnewdom Hsamedoms]. }
    iMod (update_has_fuels_no_step ζ (S <$> fs) (fs ⇂ (dom fs ∖ rem)) with "[Hf] [Hfuel] [Hamapping]") as "(Hafuels&Hfuels&Hamapping)" =>//.
    { rewrite -dom_empty_iff_L. set_solver -Hnewdom Hsamedoms Hfueldom. }
    { rewrite dom_domain_restrict; set_solver -Hnewdom Hsamedoms Hfueldom. }
    iModIntro.
    iExists {|
      ls_under := δ1.(ls_under);
      ls_fuel := _;
      ls_fuel_dom := Hfueldom;
      ls_same_doms := Hsamedoms;
    |}.
    iExists (Silent_step ζ). simpl.
    iSplit; last first.
    { rewrite (dom_fmap_L _ fs). iFrame "Hfuels". iExists _, FR. rewrite /maps_inverse_match //=. iFrame.
      assert (dom fs ⊆ dom (ls_fuel $ δ1)).
      { intros ρ Hin. setoid_rewrite dom_fmap in Hxdom.
        specialize (Hxdom ρ). rewrite -ls_same_doms. apply elem_of_dom. exists ζ.
        by apply Hxdom. }
      iSplit.
      { iApply (auth_fuel_is_proper with "Hafuels"). f_equiv.
        rewrite dom_domain_restrict; last set_solver -Hnewdom Hsamedoms Hfueldom.
        replace (dom fs ∖ (dom fs ∖ rem)) with rem; [set_solver +|].
        rewrite -leibniz_equiv_iff. intros ρ. split; [set_solver -Hnewdom Hsamedoms Hfueldom|].
        intros [? [?|?]%not_elem_of_difference]%elem_of_difference =>//. }
      iPureIntro. split; last split.
      - intros ρ ζ'. rewrite /new_mapping dom_domain_restrict; last set_solver +. split.
        + intros [Hlk Hin]%map_filter_lookup_Some. destruct (decide (ζ' = ζ)) as [->|Hneq].
          * rewrite lookup_insert. eexists; split=>//. set_solver -Hnewdom Hsamedoms Hfueldom.
          * rewrite lookup_insert_ne //. by apply Hminv.
        + intros Hin. destruct (decide (ζ' = ζ)) as [->|Hneq].
          * rewrite lookup_insert in Hin. apply map_filter_lookup_Some.
            destruct Hin as (?&?&?). simplify_eq. split; last set_solver -Hnewdom Hsamedoms Hfueldom.
            apply Hxdom. rewrite dom_fmap. set_solver -Hnewdom Hsamedoms Hfueldom.
          * rewrite lookup_insert_ne // -Hminv in Hin. apply map_filter_lookup_Some; split=>//.
            rewrite /new_dom. apply elem_of_difference; split.
            ** apply elem_of_dom_2 in Hin. rewrite ls_same_doms in Hin. set_solver -Hnewdom Hsamedoms Hfueldom.
            ** assert (ρ ∉ dom fs); last set_solver -Hnewdom Hsamedoms Hfueldom.
               rewrite dom_fmap_L in Hxdom.
               intros contra%Hxdom. congruence.
      - intros ζ0 Hnotin. apply lookup_insert_None; split.
        + apply Hlocssmall.
          destruct c1.
          have Hle := locales_of_list_step_incl _ _ _ _ _ Hstep. simpl.
          clear -Hnotin Hle. set_solver.
        + intros <-. destruct c1.
          have ? := locales_of_list_step_incl _ _ _ _ _ Hstep. simpl.
          clear Hfueldom Hsamedoms. inversion Hstep. simplify_eq.
          assert (locale_of t1 e1 ∈ locales_of_list (t1 ++ e1 :: t2));
            last by eauto.
          apply locales_of_list_from_locale_from.
          rewrite from_locale_from_Some //. 
          eapply prefixes_from_spec.
          eexists _,_. by list_simplifier.
      - rewrite Hnewdom /new_dom. apply elem_of_equiv_empty_L. intros ρ [Hin1 Hin2]%elem_of_intersection.
        assert (ρ ∈ dom (ls_fuel δ1))
               by set_solver -Hnewdom Hsamedoms Hfueldom.
        set_solver -Hnewdom Hsamedoms Hfueldom. }
    iPureIntro.
    do 2 split; first done. split; [split; [|split; [|split; [|split]]]|] =>//.
    - eexists. apply Hxdom. by rewrite dom_fmap.
    - unfold fuel_decr. simpl.
      intros ρ' Hin Hin' Hmustdec.
      rewrite Hnewdom in Hin'.

      inversion Hmustdec; simplify_eq.
      + have Hinfs: ρ' ∈ dom (S <$> fs) by set_solver.
        rewrite map_lookup_imap Hfuel // lookup_fmap. rewrite dom_fmap in Hinfs.
        rewrite lookup_gset_to_gmap option_guard_True //=.

        pose proof Hinfs as Hinfs'. apply elem_of_dom in Hinfs' as [f Heqf].
        assert (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs !! ρ' = Some f) as Heqfilter.
        { rewrite map_filter_lookup Heqf /= option_guard_True //. set_solver -Hnewdom Hsamedoms Hfueldom Hmustdec. }
        rewrite decide_True // ?Heqfilter ?lookup_fmap ?Heqf /=; last by eapply elem_of_dom_2. lia.
      + rewrite /= /new_mapping map_filter_lookup in Hneqtid.
        pose proof Hin as Hin2. rewrite -ls_same_doms in Hin2. apply elem_of_dom in Hin2 as [f Hf].
        rewrite Hf /= option_guard_True // in Hneqtid.
    - intros ρ' Hin _. simpl. destruct (decide (ρ' ∈ rem)) as [Hin'|Hnin'].
      + right; split; last set_solver -Hnewdom Hsamedoms Hfueldom.
        rewrite /fuel_apply map_imap_dom_eq ?dom_gset_to_gmap; first set_solver.
        intros ρ0 _ Hin0. 
        case_decide as Hnin; [by apply elem_of_dom|].
        apply elem_of_difference in Hin0 as [Hin1 ?].
        apply elem_of_union in Hin1 as [?|Hin2]; first by apply elem_of_dom.
        exfalso. apply Hnin. apply elem_of_dom in Hin2 as [f ?].
        eapply elem_of_dom_2. rewrite map_filter_lookup_Some. split =>//.
        apply elem_of_difference; split =>//. by eapply elem_of_dom_2.
      + left. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=;
                      last set_solver -Hnewdom Hsamedoms Hfueldom.
        apply elem_of_dom in Hin as [f Hf].
        case_decide as Hin; [|by rewrite !Hf //=].
        apply elem_of_dom in Hin as [f' Hf']. rewrite Hf'.
        apply map_filter_lookup_Some in Hf' as [Hfs Hf'].
        rewrite Hfuel ?lookup_fmap ?Hfs /=; [lia |].
        rewrite dom_fmap; set_solver -Hnewdom Hsamedoms Hfueldom.
    - rewrite Hnewdom. assert (dom fs ⊆ dom $ ls_fuel δ1);
        last set_solver -Hnewdom Hsamedoms Hfueldom.
      intros ρ Hin. apply elem_of_dom.
      rewrite Hfuel ?dom_fmap // -elem_of_dom dom_fmap //.
    - unfold tids_smaller; simpl. intros ρ ζ0 Hin.
      destruct c1.
      (* ; destruct (trace_last extr). *)
      eapply from_locale_step =>//.
      rewrite /tids_smaller /= in Hζs. eapply Hζs.
      rewrite /new_mapping map_filter_lookup_Some in Hin.
      by destruct Hin.
  Qed.
 
  Lemma actual_update_fork_split R1 R2 tp1 tp2 fs (δ1: LM) ζ efork σ1 σ2 (Hdisj: R1 ## R2):
    fs ≠ ∅ ->
    R1 ∪ R2 = dom fs ->
    (* trace_last extr = (tp1, σ1) -> *)
    locale_step (tp1, σ1) (Some ζ) (tp2, σ2) ->
    (∃ tp1', tp2 = tp1' ++ [efork] ∧ length tp1' = length tp1) ->
    has_fuels_S ζ fs -∗ model_state_interp (tp1, σ1) δ1 ==∗
      ∃ δ2, has_fuels (locale_of tp1 efork) (fs ⇂ R2) ∗ has_fuels ζ (fs ⇂ R1) ∗
            (partial_mapping_is {[ locale_of tp1 efork := ∅ ]} -∗ frag_mapping_is {[ locale_of tp1 efork := ∅ ]}) ∗
            model_state_interp (tp2, σ2) δ2
        ∧ ⌜valid_evolution_step (Some ζ) (tp2, σ2) δ1 (Silent_step ζ) δ2 (LM := LM)⌝.
  Proof.
    iIntros (Hnemp Hunioneq Hstep Htlen) "Hf Hmod".
    unfold has_fuels_S.
    simpl in *.
    iDestruct (has_fuel_fuel with "Hf Hmod") as %Hfuels.
    iDestruct (model_state_interp_tids_smaller with "Hmod") as %Hts.
    iDestruct "Hmod" as (m FR) "(Haf&Ham&HFR&%Hminv&%Hsmall&Hamod&%HFR)".
    pose Hlocincl := locales_of_list_step_incl _ _ _ _ _ Hstep.
    iMod (update_has_fuels_no_step_no_change ζ (S <$> fs) fs with "Hf Haf Ham") as "(Haf&Hf&Ham)".
    { intros contra. apply fmap_empty_inv in contra. set_solver. }
    { rewrite dom_fmap_L //. }
    iDestruct "Hf" as "(Hf & Hfuels)".
    iDestruct (frag_mapping_same with "Ham Hf") as %Hmapping.
    assert (Hnewζ: (locale_of tp1 efork) ∉ dom m).
    { apply not_elem_of_dom. apply Hsmall.
      unfold tids_smaller in Hsmall.
      rewrite elem_of_list_fmap. intros ([??]&Hloc&Hin).
      symmetry in Hloc.
      rewrite -> prefixes_from_spec in Hin.
      destruct Hin as (?&t0&?&?).
      simplify_eq. list_simplifier.
      eapply locale_injective=>//.
      apply prefixes_from_spec.
      exists t0, []. split =>//. by list_simplifier. }
    iMod (update_mapping_new_locale ζ (locale_of tp1 efork) _ R1 R2 with "Ham Hf") as "(Ham&HR1&HR2)"; eauto.
    assert (Hsamedoms: dom (map_imap
                                (λ ρ o,
                                 if decide (ρ ∈ R2) then Some $ locale_of tp1 efork else Some o)
                                (ls_mapping δ1)) =
                         dom (map_imap
                             (λ ρ o,
                              if decide (ρ ∈ R1 ∪ R2) then Some (o - 1)%nat else Some o)
                             (ls_fuel δ1))
           ).
    { rewrite !map_imap_dom_eq; first by rewrite ls_same_doms.
      - by intros ρ??; destruct (decide (ρ ∈ R1 ∪ R2)).
      - by intros ρ??; destruct (decide (ρ ∈ R2)). }
    assert (Hfueldom: live_roles _ δ1 ⊆ dom (map_imap
                             (λ ρ o,
                              if decide (ρ ∈ R1 ∪ R2) then Some (o - 1)%nat else Some o)
                             (ls_fuel δ1))).
    { rewrite map_imap_dom_eq; first by apply ls_fuel_dom.
      - by intros ρ??; destruct (decide (ρ ∈ R1 ∪ R2)). }
    iExists {|
      ls_under := δ1.(ls_under);
      ls_fuel := _;
      ls_fuel_dom := Hfueldom;
      ls_mapping := _;
      ls_same_doms := Hsamedoms;
    |}.
    iModIntro.
    assert (Hdomincl: dom fs ⊆ dom (ls_fuel δ1)).
    { intros ρ' Hin'. rewrite elem_of_dom Hfuels; last first.
      { rewrite dom_fmap_L //. }
      rewrite lookup_fmap fmap_is_Some. by apply elem_of_dom. }
    rewrite -Hunioneq big_sepS_union //. iDestruct "Hfuels" as "[Hf1 Hf2]".
    iSplitL "Hf2 HR2".
    { unfold has_fuels.
      rewrite dom_domain_restrict;
        [|set_solver -Hsamedoms Hsamedoms Hfueldom Hlocincl Hdomincl].
      iFrame.
      iApply (big_sepS_impl with "Hf2"). iIntros "!#" (x Hin) "(%f&%&?)".
      iExists _; iFrame. iPureIntro. rewrite map_filter_lookup_Some //. }    
    iSplitL "Hf1 HR1".
    { unfold has_fuels.
      rewrite dom_domain_restrict;
        [|set_solver -Hsamedoms Hsamedoms Hfueldom Hlocincl Hdomincl].
      iFrame.
      iApply (big_sepS_impl with "Hf1"). iIntros "!#" (x Hin) "(%f&%&?)".
      iExists _; iFrame. iPureIntro. rewrite map_filter_lookup_Some //. }    
    iSplitR; [iIntros; by iFrame | ].  
    iSplitL "Ham Haf Hamod HFR".
    { iExists _, FR; simpl. iFrame "Ham Hamod HFR".
      iSplit.
      - iApply (auth_fuel_is_proper with "Haf"). unfold fuel_apply.
        rewrite -leibniz_equiv_iff. intros ρ. rewrite !map_lookup_imap.
        rewrite Hunioneq dom_fmap_L difference_diag_L difference_empty_L.
        rewrite lookup_gset_to_gmap.
        destruct (decide (ρ ∈ dom (ls_fuel δ1) ∪ dom fs)) as [Hin|Hin].
        + rewrite option_guard_True //=.
          assert (Hmap: ρ ∈ dom (ls_fuel δ1)).
          { set_unfold. naive_solver. }
          destruct (decide (ρ ∈ dom fs)) as [Hinfs|Hinfs].
          * apply elem_of_dom in Hmap as [? Hinfuels]. rewrite Hinfuels /=.
            rewrite Hfuels in Hinfuels; last set_solver.
            rewrite lookup_fmap in Hinfuels.
            rewrite leibniz_equiv_iff.
            rewrite -lookup_fmap in Hinfuels.
            rewrite lookup_fmap_Some in Hinfuels.
            destruct Hinfuels as [y [<- Hinfuels]].
            rewrite Hinfuels. f_equiv. lia.
          * apply elem_of_dom in Hmap as [? Hinfuels].
            rewrite Hinfuels //.
        + rewrite option_guard_False //=.
          rewrite -> not_elem_of_union in Hin. destruct Hin as [Hin ?].
          rewrite -> not_elem_of_dom in Hin. rewrite Hin //.
      - iPureIntro. split; first last; [split|].
        { intros ζ' Hζ'. rewrite lookup_insert_ne; last first.
          { pose proof (locales_of_list_step_incl _ _ _ _ _ Hstep).
            clear Hfueldom Hsamedoms.
            assert (ζ' ∉ locales_of_list tp1) by eauto.            
            intros contra. simplify_eq.
            destruct Htlen as [tp1' [-> Hlen]].
            inversion Hstep as [? ? e1 ? e2 ? efs t1 t2 Hf1 YY Hprimstep |].
            simplify_eq.
            assert (efs = [efork]) as ->.
            { symmetry. assert (length tp1' = length (t1 ++ e2 :: t2)).
              rewrite app_length //=; rewrite app_length //= in Hlen.
              clear Hlen. eapply app_inj_1 =>//. by list_simplifier. }
            rewrite H2 in Hζ'.
            apply Hζ'. apply elem_of_list_fmap.
            eexists (t1 ++ e2 :: t2, _); split =>//.
            - erewrite locale_equiv =>//. apply locales_equiv_middle.
              eapply locale_step_preserve => //.
            - replace (t1 ++ e2 :: t2 ++ [efork]) with ((t1 ++ e2 :: t2) ++ [efork]); last by list_simplifier.
              rewrite prefixes_from_app. set_unfold; naive_solver. }
          rewrite lookup_insert_ne; last first.
          { intros <-. rewrite Hsmall in Hmapping; [congruence | naive_solver]. }
          apply Hsmall; set_unfold; naive_solver. }
        { rewrite map_imap_dom_eq // => ρ f Hin. by destruct (decide (ρ ∈ R1 ∪ R2)). }
        intros ρ ζ'. rewrite map_lookup_imap.
        destruct (decide (ρ ∈ dom (ls_mapping δ1))) as [Hin|Hin].
        + apply elem_of_dom in Hin as [ζ'' Hρ]. rewrite Hρ. simpl.
          destruct (decide (ρ ∈ R2)) as [Hin'|Hin'].
          * split.
            -- intros. simplify_eq. rewrite lookup_insert. eauto.
            -- intros (ks & Hlk & H'). destruct (decide (ζ' = locale_of tp1 efork)); first congruence.
               rewrite lookup_insert_ne // in Hlk. exfalso.
               assert (ρ ∈ dom fs).
               { set_unfold. naive_solver. }
               destruct (decide (ζ = ζ')); simplify_eq.
               ** rewrite lookup_insert in Hlk. set_unfold. naive_solver.
               ** rewrite lookup_insert_ne // in Hlk.
                  assert (ζ = ζ'); last done.
                  { eapply (maps_inverse_bij _ _ _ _ ks); eauto. }
          * split.
            -- intros ?. simplify_eq. specialize (Hminv ρ ζ').
               apply Hminv in Hρ as (?&?&?).
               destruct (decide (ζ' = locale_of tp1 efork)).
               { simplify_eq. apply not_elem_of_dom in Hnewζ.
                 simpl in Hnewζ. rewrite -> Hnewζ in *. congruence. }
               destruct (decide (ζ' = ζ)).
               { simplify_eq. assert (ρ ∈ R1); first set_solver.
                 exists R1. rewrite lookup_insert_ne // lookup_insert //. }
               rewrite lookup_insert_ne // lookup_insert_ne //. eauto.
            -- intros (ks&Hin&?).
               destruct (decide (ζ' = locale_of tp1 efork)).
               { simplify_eq. rewrite lookup_insert in Hin. set_solver. }
               rewrite lookup_insert_ne // in Hin.
               destruct (decide (ζ' = ζ)).
               { simplify_eq. rewrite lookup_insert // in Hin.
                 f_equal. simplify_eq.
                 assert (ls_mapping δ1 !! ρ = Some ζ).
                 { eapply Hminv. eexists _. split; eauto. set_unfold; naive_solver. }
                 congruence. }
               rewrite lookup_insert_ne // in Hin.
               assert (ls_mapping δ1 !! ρ = Some ζ').
               { eapply Hminv. eexists _. split; eauto. }
               congruence.
        + apply not_elem_of_dom in Hin. rewrite Hin /=. split; first done.
          intros (?&Hin'&?). rewrite -ls_same_doms in Hdomincl.
          apply not_elem_of_dom in Hin.
          destruct (decide (ζ' = locale_of tp1 efork)).
          { simplify_eq. rewrite lookup_insert in Hin'. simplify_eq.
            set_unfold; naive_solver. }
          rewrite lookup_insert_ne // in Hin'.
          destruct (decide (ζ' = ζ)).
          { simplify_eq. rewrite lookup_insert // in Hin'. simplify_eq.
            set_unfold; naive_solver. }
          rewrite lookup_insert_ne // in Hin'.
          assert (ls_mapping δ1 !! ρ = Some ζ').
          { eapply Hminv. eauto. }
          apply not_elem_of_dom in Hin. congruence. }
    iSplit; first done.
    iSplit; last first.
    { iPureIntro. intros ρ ζ'. simpl. rewrite map_lookup_imap.
      destruct (ls_mapping δ1 !!ρ) eqn:Heq; last done. simpl.
      destruct (decide (ρ ∈ R2)); first  (intros ?; simplify_eq).
      - destruct Htlen as [tp1' [-> Hlen]].
        inversion Hstep as [? ? e1 ? e2 ? efs t1 t2 Hf1 YY Hprimstep |]. simplify_eq.
        assert (efs = [efork]) as ->.
        { symmetry. assert (length tp1' = length (t1 ++ e2 :: t2)).
          rewrite app_length //=; rewrite app_length //= in Hlen.
          clear Hlen. eapply app_inj_1 =>//. by list_simplifier. }
        assert (is_Some (from_locale (t1 ++ e1 :: t2 ++ [efork]) (locale_of (t1 ++ e1 :: t2) efork))).
        + unfold from_locale. erewrite from_locale_from_Some; eauto.
          apply prefixes_from_spec. list_simplifier. eexists _, []. split=>//.
          by list_simplifier.
        + eapply from_locale_from_equiv =>//; [constructor |]. rewrite H0.
          replace (t1 ++ e1 :: t2 ++ [efork]) with ((t1 ++ e1 :: t2) ++ [efork]);
            last by list_simplifier.
          replace (t1 ++ e2 :: t2 ++ [efork]) with ((t1 ++ e2 :: t2) ++ [efork]);
            last by list_simplifier.
          assert (locales_equiv (t1 ++ e1 :: t2) (t1 ++ e2 :: t2)).
          { apply locales_equiv_middle. eapply locale_step_preserve =>//. }
          apply locales_equiv_from_app =>//.
          by eapply locales_equiv_from_refl.
      - intros ?; simplify_eq.
        assert (is_Some (from_locale tp1 ζ')) by eauto.
        eapply from_locale_step =>//. }
    iSplit.
    { iPureIntro. destruct (map_choose _ Hnemp) as [ρ[??]]. exists ρ.
      apply Hminv. eexists _. split; eauto. apply elem_of_dom. eauto. }
    iSplit.
    { iPureIntro. intros ρ Hlive Hlive' Hmd. simpl. inversion Hmd; simplify_eq.
      - rewrite map_lookup_imap.
        assert (Hin: ρ ∈ dom (ls_fuel δ1)).
        { rewrite -ls_same_doms elem_of_dom. eauto. }
        apply elem_of_dom in Hin. destruct Hin as [f' Hin'].
        rewrite Hin' /=.
        destruct (decide (ρ ∈ R1 ∪ R2)) as [Hin''|Hin''].
        { rewrite dom_fmap_L -Hunioneq in Hfuels.
          specialize (Hfuels _ Hin''). rewrite lookup_fmap Hin' in Hfuels.
          destruct (fs !! ρ); simplify_eq. simpl in Hfuels. injection Hfuels.
          intros ->. simpl. lia. }
        symmetry in Hsametid. apply Hminv in Hsametid as (?&?&?).
        set_unfold; naive_solver.
      - rewrite map_lookup_imap. simpl in *. clear Hmd.
        destruct (decide (ρ ∈ dom (ls_mapping δ1))) as [Hin|Hin]; last first.
        { apply not_elem_of_dom in Hin. rewrite map_lookup_imap Hin //= in Hissome. by inversion Hissome. }
        apply elem_of_dom in Hin as [ζ' Hin'].
        rewrite map_lookup_imap Hin' /= in Hneqtid.
        destruct (decide (ρ ∈ R2)) as [Hin''|Hin'']; last done.
        rewrite Hfuels; last (set_unfold; naive_solver). rewrite lookup_fmap.
        assert (Hindom: ρ ∈ dom fs); first by set_unfold; naive_solver.
        apply elem_of_dom in Hindom as [f Hindom]. rewrite Hindom /= decide_True /=; [lia|set_unfold; naive_solver]. }
    iSplit.
    { iPureIntro. intros ρ' Hρ' _. simpl. left.
      rewrite map_lookup_imap. rewrite elem_of_dom in Hρ'.
      destruct Hρ' as [f Hf]. rewrite Hf /=. destruct (decide ((ρ' ∈ R1 ∪ R2))); simpl; lia. }
    iSplit; [simpl| done]. rewrite map_imap_dom_eq //.
    by intros ρ??; destruct (decide (ρ ∈ R1 ∪ R2)).
  Qed.

  Ltac by_contradiction :=
    match goal with
    | |- ?goal => destruct_decide (decide (goal)); first done; exfalso
    end.

  (* TODO: move to upstream *)
  Lemma disjoint_subseteq:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C},
    `{Set_ A C} → ∀ X1 X2 Y1 Y2: C, X1 ⊆ Y1 -> X2 ⊆ Y2 → Y1 ## Y2 -> X1 ## X2.
  Proof. intros. set_solver. Qed. 

  Lemma union_intersection_difference_equiv_L:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C},
    Set_ A C → LeibnizEquiv C →
    ∀ X Y: C, (forall y, Decision (y ∈ Y)) ->
    X ≡ X ∩ Y ∪ X ∖ Y.
  Proof.
    intros. apply set_equiv_subseteq. split; [| set_solver].
    apply elem_of_subseteq. intros x ?.
    destruct (decide (x ∈ Y)); set_solver.
  Qed. 

  Lemma actual_update_step_still_alive
        tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ (δ1 : LM) ζ fr1 fr_stash:
    (live_roles _ s2 ∖ live_roles _ s1) ⊆ fr1 ->
    fr_stash ⊆ dom fs1 ->
    (live_roles _ s1) ∩ (fr_stash ∖ {[ ρ ]}) = ∅ ->
    dom fs2 ∩ fr_stash = ∅ ->
    (* trace_last extr = (tp1, σ1) → *)
    (* trace_last auxtr = δ1 -> *)
    locale_step (tp1, σ1) (Some ζ) (tp2, σ2) ->
    fmtrans _ s1 (Some ρ) s2 -> valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := LM) ->
    has_fuels ζ fs1 -∗ frag_model_is s1 -∗ model_state_interp (tp1, σ1) δ1 -∗
    frag_free_roles_are fr1
    ==∗ ∃ (δ2: LM) ℓ,
        ⌜labels_match (Some ζ) ℓ ∧
          (* valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[ℓ]: δ2) *)
          valid_evolution_step (Some ζ) (tp2, σ2) δ1 ℓ δ2 (LM := LM)
            ⌝
        ∗ has_fuels ζ fs2 ∗ frag_model_is s2 ∗ model_state_interp (tp2, σ2) δ2 ∗
        frag_free_roles_are (fr1 ∖ (live_roles _ s2 ∖ live_roles _ s1) ∪ fr_stash).
  Proof.
    iIntros (Hfr_new Hstash_own Hstash_dis Hstash_rem Hstep Htrans Hfuelsval) "Hfuel Hmod Hsi Hfr1".

    assert (Hfsne: fs1 ≠ ∅).
    { destruct Hfuelsval as (_&_&?&_). intros ->. set_solver. }

    iDestruct (has_fuel_in with "Hfuel Hsi") as "%Hxdom"; eauto.
    iDestruct (has_fuel_fuel with "Hfuel Hsi") as %Hfuel; eauto.
    iDestruct (model_state_interp_tids_smaller with "Hsi") as %Hless.

    iDestruct "Hsi" as "(%m&%FR&Hafuel&Hamapping&HFR&%Hinv&%Hsmall&Hamod&%HFR)".
    iDestruct (model_agree with "Hamod Hmod") as "%Heq".

    iDestruct (free_roles_inclusion with "HFR Hfr1") as %HfrFR.

    assert (Hsamedoms:
             dom (map_imap
                    (λ ρ' _, if decide (ρ' ∈ dom $ ls_fuel δ1) then ls_mapping δ1 !! ρ' else Some ζ)
                    (gset_to_gmap 333 ((dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2)))) =
               dom (update_fuel_resource δ1 fs1 fs2 s2)).
    { unfold update_fuel_resource, fuel_apply. rewrite -leibniz_equiv_iff.
      intros ρ'; split.
      - intros Hin. destruct (decide (ρ' ∈ dom fs2)) as [[f Hin1]%elem_of_dom|Hin1].
        + apply elem_of_dom. eexists f. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=.
          rewrite decide_True //. apply elem_of_dom. rewrite Hin1; eauto.
          rewrite map_imap_dom_eq dom_gset_to_gmap in Hin; first set_solver.
          intros ρ0??. destruct (decide (ρ0 ∈ dom $ ls_fuel δ1)); [|done].
          apply elem_of_dom. rewrite ls_same_doms. SS.
        + rewrite map_imap_dom_eq dom_gset_to_gmap; last first.
          { intros ρ0 ? Hin0. destruct (decide (ρ0 ∈ dom fs2)) as [|Hnotin]; apply elem_of_dom; first done.
            unfold valid_new_fuelmap in Hfuelsval.
            destruct Hfuelsval as (_&_&_&_& Hdomfs2). set_solver. }

          rewrite map_imap_dom_eq dom_gset_to_gmap in Hin; first set_solver.
          intros ρ0??. destruct (decide (ρ0 ∈ dom $ ls_fuel δ1)); [|done].
          apply elem_of_dom. rewrite ls_same_doms. SS.
      - intros [f Hin]%elem_of_dom. rewrite map_lookup_imap in Hin.
        rewrite map_imap_dom_eq dom_gset_to_gmap.
        + by_contradiction. rewrite lookup_gset_to_gmap option_guard_False // in Hin.
        + intros ρ0??. destruct (decide (ρ0 ∈ dom $ ls_fuel δ1)); [|done].
          apply elem_of_dom. rewrite ls_same_doms. SS. }

    assert (Hnewdom: dom (update_fuel_resource δ1 fs1 fs2 s2) =
                       (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2)).
    { unfold update_fuel_resource, fuel_apply. rewrite map_imap_dom_eq ?dom_gset_to_gmap //.
      intros ρ' _ Hin. destruct (decide (ρ' ∈ dom fs2)); apply elem_of_dom =>//. set_solver. }

    assert (Hfueldom: live_roles _ s2 ⊆ dom $ update_fuel_resource δ1 fs1 fs2 s2).
    { rewrite -Hsamedoms map_imap_dom_eq dom_gset_to_gmap //.
      { epose proof ls_fuel_dom as Hfueldom. intros ρ' Hin.
        destruct Hfuelsval as (?&?&?&?&?&Hdom_le).
        destruct (decide (ρ' ∈ live_roles _ δ1)).
        - apply elem_of_difference.
          split; [set_solver -Hnewdom Hsamedoms Hdom_le|].
          intros [? Habs]%elem_of_difference.
          destruct (decide (ρ' = ρ)).
          + simplify_eq. apply not_elem_of_dom in Habs.
            rewrite -> Habs in *. simpl in *. eauto.
          + apply Habs.
            assert (ρ' ∈ dom fs1 ∖ {[ρ]}); set_solver -Hnewdom Hsamedoms.
        - apply elem_of_difference.
          split; [apply elem_of_union; right; set_unfold; naive_solver|
                   set_unfold; naive_solver]. }
      intros ρ0??. destruct (decide (ρ0 ∈ dom $ ls_fuel δ1)); [|done].
      apply elem_of_dom. rewrite ls_same_doms. SS. }
    iExists {|
      ls_under := s2;
      ls_fuel :=  _;
      ls_fuel_dom := Hfueldom;
      ls_mapping := _;
      ls_same_doms := Hsamedoms;
    |}, (Take_step ρ ζ).
    Unshelve.
    iMod (update_has_fuels _ fs1 fs2 with "Hfuel Hafuel Hamapping") as "(Hafuel & Hfuel & Hmapping)".
    { set_solver. }
    { unfold valid_new_fuelmap in Hfuelsval.
      destruct Hfuelsval as (_&_&?&?& Hfs2_inf&Hfs2_sup).
      apply elem_of_equiv_empty_L => ρ0 Hin.
      apply elem_of_intersection in Hin as [Hin1 Hin2].
      apply elem_of_difference in Hin1 as [Hin11 Hin12].
      assert (ρ0 ∈ live_roles _ s2 ∖ live_roles _ s1)
             by set_solver -Hsamedoms Hnewdom.
      assert (ρ0 ∈ fr1) by set_solver -Hsamedoms Hnewdom.
      assert (ρ0 ∈ FR) by set_solver -Hsamedoms Hnewdom.
      assert (ρ0 ∉ dom (ls_fuel δ1)) by set_solver -Hsamedoms Hnewdom.
      done. }
    iMod (update_model s2 with "Hamod Hmod") as "[Hamod Hmod]".


    (* iMod (update_free_roles (live_roles M s2 ∖ live_roles M s1) *)
    (*        with "HFR Hfr1") as "[HFR Hfr2]"; [set_solver|]. *)
    pose proof (proj1 (subseteq_disjoint_union_L _ _) HfrFR) as [FR' [FR_EQ DISJ']].
    iMod (update_free_roles_strong fr1 (fr1 ∖ (live_roles _ s2 ∖ live_roles _ s1) ∪ fr_stash) FR' with "[HFR] [Hfr1]") as "[HFR Hfr2]"; auto.
    { apply disjoint_union_l. split; [set_solver| ].
      eapply disjoint_subseteq.
      { apply _. } (* TODO: why is it needed explicitly? *)
      { apply Hstash_own. }
      { eapply subseteq_proper; [reflexivity|..].
        { apply leibniz_equiv_iff, FR_EQ. }
        set_solver. }
      rewrite -ls_same_doms in HFR.
      clear -HFR Hxdom.
      eapply disjoint_subseteq; [apply _| |reflexivity|].
      2: { symmetry. apply disjoint_intersection. apply leibniz_equiv_iff, HFR. }
      apply elem_of_subseteq. intros ? ?%Hxdom.
      eapply elem_of_dom_2; eauto. }
    { by rewrite FR_EQ. }
    
    iModIntro. iSplit.
    { iSplit; first done. iPureIntro.
      destruct Hfuelsval as (Hlim&Hzombie&Hinfs1m&Hnewlim&Hdec&Hinf&Hsup).
      constructor =>//; split.
      - constructor; simpl; first by rewrite Heq //.
        split; first by apply Hxdom; set_solver.
        split.
        { intros ? ? Hdom Hmd. inversion Hmd; clear Hmd; simplify_eq.
          + symmetry in Hsametid. rewrite -> Hxdom in Hsametid. simpl.
            unfold update_fuel_resource, fuel_apply.
            rewrite map_lookup_imap lookup_gset_to_gmap.
            destruct (decide (ρ' ∈ live_roles M s2 ∪ dom fs2)) as [Hin|Hin].
            * rewrite option_guard_True //=.
              { destruct (decide (ρ' ∈ dom fs2)) as [Hin2|Hin2].
                ** rewrite Hfuel; last set_solver.
                   apply Hdec; [congruence|set_solver -Hsamedoms Hnewdom Hdom].
                ** exfalso. set_solver -Hsamedoms Hnewdom Hdom. }
              apply elem_of_difference; split;
                [set_solver -Hsamedoms Hnewdom Hdom|].
              apply not_elem_of_difference; right.
              apply elem_of_union in Hin as [|]; [|done].
              destruct (decide (ρ' = ρ)); simplify_eq.
              apply Hinf; set_solver -Hsamedoms Hnewdom Hdom.
            * rewrite option_guard_False //=.
              ** assert (ρ' ∈ dom fs2); set_solver -Hsamedoms Hnewdom Hdom.
              ** apply not_elem_of_difference; right; set_solver -Hsamedoms Hnewdom Hdom.
          + simpl in *. unfold update_fuel_resource, fuel_apply.
            rewrite map_lookup_imap lookup_gset_to_gmap.

            destruct (decide (ρ' ∈ (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hin|Hin].
            * rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //= decide_True //= in Hneqtid.
            * apply not_elem_of_difference in Hin as [?|Hin];
                [set_solver -Hsamedoms Hnewdom Hdom|].
              apply elem_of_difference in Hin as [??].
              rewrite map_lookup_imap lookup_gset_to_gmap /= option_guard_False /= in Hissome;
                [inversion Hissome; congruence|set_solver -Hsamedoms Hnewdom Hdom].
          + simpl in *. rewrite Hfuel; last set_solver -Hsamedoms Hnewdom Hdom.
            unfold update_fuel_resource, fuel_apply.
            rewrite Hnewdom in Hnotdead. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=.
            assert (ρ' ∈ dom fs2) by (set_solver -Hsamedoms Hnewdom Hdom).
           rewrite decide_True; [apply Hzombie =>//; set_solver -Hsamedoms Hnewdom Hdom | done]. }
        split.
        + intros ? Hin ?. simplify_eq; simpl.
          unfold update_fuel_resource, fuel_apply.
          rewrite map_lookup_imap lookup_gset_to_gmap.
          destruct (decide (ρ' ∈ (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hlive|Hlive].
          * rewrite option_guard_True //=.
            apply elem_of_difference in Hlive as [Hin1 Hnin].
            apply not_elem_of_difference in Hnin.
            destruct (decide (ρ' ∈ dom fs2)) as [Hin2|Hin2].
            ** destruct (decide (ρ' ∈ live_roles _ δ1)); left.
               *** destruct (decide (ρ' ∈ dom fs1)).
                   { rewrite Hfuel //. apply oleq_oless, Hdec; [congruence|set_solver -Hsamedoms Hnewdom]. }
                   { exfalso. set_solver -Hsamedoms Hnewdom. }
               *** assert (ρ' ∉ live_roles _ s2).
                   { by_contradiction. assert (ρ' ∈ fr1); [eapply elem_of_subseteq; eauto; set_solver -Hsamedoms Hnewdom|].
                     assert (ρ' ∈ (fr1 ∪ FR')); [eapply elem_of_subseteq; eauto; set_solver -Hsamedoms Hnewdom|set_solver -Hsamedoms Hnewdom]. }
                   assert (ρ' ∈ dom fs1) by set_solver -Hsamedoms Hnewdom.
                   rewrite Hfuel //. apply oleq_oless, Hdec; [congruence|set_solver -Hsamedoms Hnewdom].
            ** left. rewrite elem_of_dom in Hin. destruct Hin as [? ->]. simpl;lia.
          * right; split.
            ** eapply not_elem_of_weaken; [|by apply map_imap_dom_inclusion; rewrite dom_gset_to_gmap].
               rewrite dom_gset_to_gmap //.
            ** apply not_elem_of_difference in Hlive as [?|Hlive]; [set_solver -Hsamedoms Hnewdom|].
               apply elem_of_difference in Hlive as [? Habs].
               exfalso. apply Habs. set_solver -Hsamedoms Hnewdom Hfueldom.
        + split.
          { intros Hlive. unfold update_fuel_resource, fuel_apply.
          destruct (decide (ρ ∈ (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hin|Hnin].
          - rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=. 
            rewrite decide_True; [by apply Hlim |set_solver -Hsamedoms Hnewdom Hfueldom].
          - exfalso; apply not_elem_of_difference in Hnin as [Hnin|Hnin].
            + assert (ρ ∉ live_roles _ δ1).
              eapply not_elem_of_weaken => //.
              { epose proof ls_fuel_dom. set_solver -Hsamedoms Hnewdom Hfueldom. }
              assert (ρ ∈ dom fs2) by set_solver -Hsamedoms Hnewdom Hfueldom. set_solver -Hsamedoms Hnewdom Hfueldom.
            + apply elem_of_difference in Hnin as [? Hnin].
              apply not_elem_of_dom in Hnin. rewrite Hnin /= in Hlim.
              by apply Hlim. }
          split.
          { intros ρ'. unfold update_fuel_resource, fuel_apply => Hin.
            rewrite map_imap_dom_eq in Hin; last first.
            { intros ρ0 _ Hin'. destruct (decide (ρ0 ∈ dom fs2)); [by apply elem_of_dom|].
              rewrite dom_gset_to_gmap elem_of_difference in Hin'.
              destruct Hin' as [Hin' ?]. apply elem_of_union in Hin' as [?|?]; [by apply elem_of_dom|done]. }
            rewrite dom_gset_to_gmap in Hin. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True /=; last set_solver -Hsamedoms Hnewdom Hfueldom.
            assert (ρ' ∈ dom fs2) by set_solver -Hsamedoms Hnewdom Hfueldom. rewrite decide_True //. apply Hnewlim. apply elem_of_difference; split =>//.
            intros contra%Hxdom%elem_of_dom_2. rewrite ls_same_doms in contra. simplify_eq. set_solver -Hsamedoms Hnewdom Hfueldom. }
          intros ρ0 Hin.
          assert (ρ0 ∉ live_roles _ δ1).
          { eapply not_elem_of_weaken; last apply ls_fuel_dom. set_solver -Hsamedoms Hnewdom Hfueldom. }
          apply elem_of_difference in Hin as [Hin1 Hnin].
          assert (ρ0 ∈ live_roles _ s2).
          { by_contradiction.
            assert (ρ0 ∈ dom fs2).
            { unfold update_fuel_resource, fuel_apply in Hin1.
              eapply elem_of_subseteq in Hin1; last apply map_imap_dom_inclusion.
              rewrite dom_gset_to_gmap in Hin1. set_solver -Hsamedoms Hnewdom Hfueldom. }
            exfalso. assert (Hinabs: ρ0 ∈ dom fs1) by set_solver -Hsamedoms Hnewdom Hfueldom.
            apply not_elem_of_dom in Hnin. rewrite Hfuel // in Hnin.
            apply elem_of_dom in Hinabs. rewrite Hnin in Hinabs. simpl in Hinabs.
            by inversion Hinabs. }
          set_solver -Hsamedoms Hnewdom Hfueldom.
      - simplify_eq. unfold tids_smaller; simpl.
        intros ρ' ? Hmim.
        rewrite map_lookup_imap in Hmim. rewrite lookup_gset_to_gmap in Hmim.
        destruct (decide (ρ' ∈ (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2)));
          last by rewrite option_guard_False in Hmim.
        rewrite option_guard_True //= in Hmim.
        destruct (decide (ρ' ∈ dom (ls_fuel δ1))).
        + inversion Hstep; simplify_eq.
          eapply from_locale_step =>//. by eapply Hless.
        + simplify_eq.
          inversion Hstep; simplify_eq.
          eapply from_locale_step =>//. unfold from_locale. rewrite from_locale_from_Some //.
          apply prefixes_from_spec. exists t1, t2. by list_simplifier. }

    iFrame "Hfuel Hmod Hfr2". iExists _, _. iFrame. all: eauto. (* TODO: find source... *)
    iPureIntro; split.

    { intros ρ' ζ'. simpl. rewrite map_lookup_imap.
      rewrite lookup_gset_to_gmap //=.
      destruct (decide (ρ' ∈ (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hin|Hnotin].
      - rewrite option_guard_True //=. destruct (decide (ρ' ∈ dom (ls_fuel δ1))).
        + destruct (decide (ζ' = ζ)) as [->|Hneq].
          * rewrite lookup_insert. split.
            { eexists; split =>//. apply elem_of_difference in Hin as [? Hin].
              apply not_elem_of_difference in Hin as [?|?]; [|done].
              set_solver -Hsamedoms Hnewdom Hfueldom. }
            { intros (?&?&?). simplify_eq. apply Hxdom.
              destruct Hfuelsval as (?&?&?&?&?). by_contradiction.
              assert (ρ' ∈ live_roles M s2 ∖ live_roles M δ1) by set_solver -Hsamedoms Hnewdom Hfueldom.
              assert (ρ' ∈ fr1) by set_solver -Hsamedoms Hnewdom Hfueldom.
              assert (ρ' ∈ (fr1 ∪ FR')) by set_solver -Hsamedoms Hnewdom Hfueldom.
              assert (ρ' ∉ dom $ ls_fuel δ1) by set_solver -Hsamedoms Hnewdom Hfueldom.
              done. }
          * rewrite lookup_insert_ne //.
        + split.
          * intros Htid. simplify_eq. rewrite lookup_insert. eexists; split=>//.
            set_solver -Hsamedoms Hnewdom Hfueldom.
          * assert (ρ' ∈ dom fs2) by set_solver -Hsamedoms Hnewdom Hfueldom. intros Hm. by_contradiction.
            rewrite lookup_insert_ne in Hm; last congruence.
            rewrite -Hinv in Hm. apply elem_of_dom_2 in Hm. rewrite ls_same_doms // in Hm.
      - destruct Hfuelsval as (?&?&?&?&Hinf&?). rewrite option_guard_False //=. split; first done.
        destruct (decide (ζ' = ζ)) as [->|Hneq].
        { rewrite lookup_insert //. intros (?&?&?). simplify_eq. set_solver -Hsamedoms Hnewdom Hfueldom. }
        rewrite lookup_insert_ne //.
        rewrite -Hinv. intros Habs.

        apply not_elem_of_difference in Hnotin as [Hnin|Hin].
        + apply elem_of_dom_2 in Habs. rewrite ls_same_doms in Habs. set_solver -Hsamedoms Hnewdom Hfueldom.
        + apply elem_of_difference in Hin as [Hin Hnin].
          apply Hxdom in Hin. congruence. }
    split.
    { intros ζ' ?. pose proof (locales_of_list_step_incl _ _ _ _ _ Hstep). simpl.
      rewrite lookup_insert_ne; first by apply Hsmall; set_solver -Hsamedoms Hnewdom Hfueldom.
      intros <-. destruct Hfuelsval as (_&_&Hfs1&_).
      rewrite <-Hxdom in Hfs1. apply Hinv in Hfs1 as (?&HM&?).
      rewrite Hsmall // in HM. set_solver -Hsamedoms Hnewdom Hfueldom. }
    { simpl. rewrite /update_fuel_resource /fuel_apply.
      rewrite map_imap_dom_eq ?dom_gset_to_gmap.
      + apply elem_of_equiv_empty_L. intros ρ' [Hin1 Hin2]%elem_of_intersection.

        (* TODO: problems with elem_of_proper *)
        assert (fr1 ∖ (live_roles M s2 ∖ live_roles M s1) ∪ fr_stash ∪ FR' ≡ FR ∖ (live_roles M s2 ∖ live_roles M s1) ∪ fr_stash ∪ FR' ∩ (live_roles M s2 ∖ live_roles M s1)) as ALT.
        { set_solver. }
        rewrite ALT in Hin1. 

        apply elem_of_union in Hin1 as [[Hin1 | Hin1] %elem_of_union | Hin1].
        2, 3: set_solver. 
        apply elem_of_difference in Hin1 as [Hin11 Hin12].
        apply not_elem_of_difference in Hin12.
        apply elem_of_difference in Hin2 as [Hin21 Hin22].
        apply not_elem_of_difference in Hin22.
        assert (ρ' ∉ dom $ ls_fuel δ1) by set_solver -Hsamedoms Hnewdom Hfueldom.
        assert (ρ' ∈ dom fs2) by set_solver -Hsamedoms Hnewdom Hfueldom.
        destruct Hin12 as [Hin12|Hin12]; last by (epose proof ls_fuel_dom; set_solver -Hsamedoms Hnewdom Hfueldom).
        destruct Hfuelsval as (?&?&?&?&?&?).
        assert (ρ' ∉ dom fs1); last set_solver -Hsamedoms Hnewdom Hfueldom.
        intros contra. pose proof (Hfuel _ contra) as Habs. apply elem_of_dom in contra as [? contra].
        rewrite contra in Habs. apply elem_of_dom_2 in Habs. done. 
    + intros ρ' _ Hin. destruct (decide (ρ' ∈ dom fs2)) as [Hin'|].
      * apply elem_of_dom in Hin' as [? ->]. done.
      * assert (ρ' ∈ dom (ls_fuel δ1)) as Hin' by set_solver -Hsamedoms Hnewdom Hfueldom. apply elem_of_dom in Hin' as [? ->]. done. }
  Qed.

  (* Lemma bupd_fupd_empty `{FUpd (iProp Σ)} (P: iProp Σ): *)
  (*     (|==> P)%I ⊢ |={∅}=> P. *)
  (* Proof using.  *)
  (*   iIntros "UP". *)
  (*   iDestruct (bupd_fupd ∅ with "UP") as "FP". *)
  (*   iApply "FP".  *)
  (*   (* Set Printing All. *) *)

End ActualOwnershipImpl.
