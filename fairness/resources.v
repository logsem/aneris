From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness.heap_lang Require Import heap_lang_defs. 
From trillium.fairness Require Import utils fairness fuel fuel_ext. 
From trillium.fairness Require Import partial_ownership.

Class fairnessGpreS `(LM: LiveModel Λ M) Σ `{Countable (locale Λ)} := {   
  fairnessGpreS_model :> inG Σ (authUR (optionR (exclR (ModelO M))));
  fairnessGpreS_model_mapping :> inG Σ (authUR (gmapUR (localeO Λ) (exclR (gsetR (RoleO M)))));
  fairnessGpreS_model_fuel :> inG Σ (authUR (gmapUR (RoleO M) (exclR natO)));
  fairnessGpreS_model_free_roles :> inG Σ (authUR (gset_disjUR (RoleO M)));
}.

Class fairnessGS `(LM : LiveModel Λ M) Σ `{Countable (locale Λ)} := FairnessGS {
  fairness_inG :> fairnessGpreS LM Σ;
  (** Underlying model *)
  fairness_model_name : gname;
  (** Mapping of threads to sets of roles *)
  fairness_model_mapping_name : gname;
  (** Mapping of roles to fuel *)
  fairness_model_fuel_name : gname;
  (** Set of free/availble roles *)
  fairness_model_free_roles_name : gname;
}.

Global Arguments fairnessGS {_ _} LM Σ {_ _}.
Global Arguments FairnessGS {_ _} LM Σ {_ _ _} _ _ _.
Global Arguments fairness_model_name {_ _ LM Σ _ _} _.
Global Arguments fairness_model_mapping_name {Λ M LM Σ _ _} _ : assert.
Global Arguments fairness_model_fuel_name {Λ M LM Σ _ _} _ : assert.
Global Arguments fairness_model_free_roles_name {Λ M LM Σ _ _} _ : assert.

Definition fairnessΣ Λ M `{Countable (locale Λ)} : gFunctors := #[
   GFunctor (authUR (optionUR (exclR (ModelO M))));
   GFunctor (authUR (gmapUR (localeO Λ) (exclR (gsetR (RoleO M)))));
   GFunctor (authUR (gmapUR (RoleO M) (exclR natO)));
   GFunctor (authUR (gset_disjUR (RoleO M)))
].

Global Instance subG_fairnessGpreS {Σ} `{LM : LiveModel Λ M} `{Countable (locale Λ)} :
  subG (fairnessΣ Λ M) Σ -> fairnessGpreS LM Σ.
Proof. solve_inG. Qed. 

Notation "f ⇂ R" := (filter (λ '(k,v), k ∈ R) f) (at level 30).


Section model_state_interp.
  Context `{LM: LiveModel Λ M}.
  Context `{Countable (locale Λ)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  Notation Role := (M.(fmrole)).

  Definition auth_fuel_is (F: gmap Role nat): iProp Σ :=
    own (fairness_model_fuel_name fG)
        (● (fmap (λ f, Excl f) F : ucmra_car (gmapUR (RoleO M) (exclR natO)))).

  Definition frag_fuel_is (F: gmap Role nat): iProp Σ :=
    own (fairness_model_fuel_name fG)
        (◯ (fmap (λ f, Excl f) F : ucmra_car (gmapUR (RoleO M) (exclR natO)))).

  Definition auth_mapping_is (m: gmap (locale Λ) (gset Role)): iProp Σ :=
    own (fairness_model_mapping_name fG)
        (● ( (fmap (λ (f: gset M.(fmrole)), Excl f) m) :
              ucmra_car (gmapUR _ (exclR (gsetR (RoleO M))))
        )).

  Definition frag_mapping_is (m: gmap (locale Λ) (gset Role)): iProp Σ :=
    own (fairness_model_mapping_name fG)
        (◯ ( (fmap (λ (f: gset M.(fmrole)), Excl f) m) :
              ucmra_car (gmapUR _ (exclR (gsetR (RoleO M))))
        )).

  Definition auth_model_is (fm: M): iProp Σ :=
    own (fairness_model_name fG) (● Excl' fm).

  Definition frag_model_is (fm: M): iProp Σ :=
    own (fairness_model_name fG) (◯ Excl' fm).

  Definition auth_free_roles_are (FR: gset Role): iProp Σ :=
    own (fairness_model_free_roles_name fG) (● (GSet FR)).

  Definition frag_free_roles_are (FR: gset Role): iProp Σ :=
    own (fairness_model_free_roles_name fG) (◯ (GSet FR)).

  Definition model_state_interp (* (σ: cfg Λ) *) (δ: lm_ls LM): iProp Σ :=
    ∃ FR, auth_fuel_is δ.(ls_fuel) ∗ auth_mapping_is (ls_tmap δ) ∗ 
          auth_free_roles_are FR ∗
          (* ⌜maps_inverse_match δ.(ls_mapping) M⌝ ∗ *)
          (* ⌜ ∀ ζ, ζ ∉ locales_of_list σ.1 → ls_tmap δ !! ζ = None ⌝ ∗ *)
          auth_model_is δ ∗ ⌜ FR ∩ dom δ.(ls_fuel) = ∅ ⌝.

  (* Lemma model_state_interp_tids_smaller δ σ : *)
  (*   model_state_interp σ δ -∗ ⌜ tids_smaller σ.1 δ ⌝. *)
  (* Proof. *)
  (*   iIntros "(%FR&_&_&_&%Hbig&_)". iPureIntro. *)
  (*   set (m := ls_tmap δ). pose proof (ls_mapping_tmap_corr δ (LM := LM)) as Hminv.  *)
  (*   intros ρ ζ Hin.  *)
  (*   assert (¬ (ζ ∉ locales_of_list σ.1)). *)
  (*   - intros contra. *)
  (*     apply Hminv in Hin as [? [Hsome _]]. *)
  (*     specialize (Hbig _ contra). *)
  (*     by rewrite Hbig in Hsome. *)
  (*   - destruct (decide (ζ ∈ locales_of_list σ.1)) as [Hin'|] =>//. *)
  (*     apply elem_of_list_fmap in Hin' as [[? e'] [-> Hin']]. *)
  (*     unfold from_locale. exists e'. by apply from_locale_from_Some. *)
  (* Qed. *)
  
  Global Instance frag_free_roles_are_proper: Proper (equiv ==> equiv) frag_free_roles_are.
  Proof. intros ???. set_solver. Qed.    

  Global Instance frag_mapping_is_proper: Proper (equiv ==> equiv) frag_mapping_is.
  Proof. intros ???. set_solver. Qed. 

  Lemma empty_frag_free_roles:
    ⊢ |==> frag_free_roles_are ∅.
  Proof. iApply own_unit. Qed. 

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

End model_state_interp.

Lemma own_proper `{inG Σ X} γ (x y: X):
  x ≡ y ->
  own γ x -∗ own γ y.
Proof. by intros ->. Qed.

Lemma auth_fuel_is_proper `{fairnessGS (LM:=LM) Σ}
      (x y : gmap (fmrole M) nat):
  x = y ->
  auth_fuel_is x -∗ auth_fuel_is y.
Proof. by intros ->. Qed.


Section model_state_lemmas.
  Context `{LM: LiveModel Λ M}.
  Context `{Countable (locale Λ)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  (* TODO: decide what to do with notations *)
  Notation "tid ↦M R" := (frag_mapping_is {[ tid := R ]}) (at level 33).
  Notation "tid ↦m ρ" := (frag_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
  Notation "ρ ↦F f" := (frag_fuel_is {[ ρ := f ]}) (at level 33).

  Lemma frag_mapping_same ζ m R:
    auth_mapping_is m -∗ ζ ↦M R -∗ ⌜ m !! ζ = Some R ⌝.
  Proof.
    iIntros "Ha Hf". iCombine "Ha Hf" as "H". rewrite own_valid.
    iDestruct "H" as "%Hval". iPureIntro.
    apply auth_both_valid in Hval as [HA HB].
    rewrite map_fmap_singleton in HA.
    specialize (HA 0%nat).
    apply cmra_discrete_included_iff in HA.
    apply -> (@singleton_included_l (locale Λ)) in HA. destruct HA as (R' & HA & Hsub).
    assert (✓ Some R'). by rewrite -HA.
    destruct R' as [R'|]; last done.
    apply Excl_included in Hsub. apply leibniz_equiv in Hsub.
    rewrite Hsub.
    apply leibniz_equiv in HA. rewrite -> lookup_fmap_Some in HA.
    destruct HA as (?&?&?). congruence.
  Qed.

  Lemma update_model δ δ1 δ2:
    auth_model_is δ1 -∗ frag_model_is δ2 ==∗ auth_model_is δ ∗ frag_model_is δ.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "[??]" ; eauto.
    - by apply auth_update, option_local_update, (exclusive_local_update _ (Excl δ)).
    - iModIntro. iFrame.
  Qed.

  Lemma free_roles_inclusion FR fr:
    auth_free_roles_are FR -∗
    frag_free_roles_are fr -∗
    ⌜fr ⊆ FR⌝.
  Proof.
    iIntros "HFR Hfr".
    iDestruct (own_valid_2 with "HFR Hfr") as %Hval. iPureIntro.
    apply auth_both_valid_discrete in Hval as [??].
    by apply gset_disj_included.
  Qed.

  Lemma update_free_roles rem FR fr1:
    rem ⊆ fr1 ->
    auth_free_roles_are FR -∗
    frag_free_roles_are fr1 ==∗
    auth_free_roles_are (FR ∖ rem) ∗
    frag_free_roles_are (fr1 ∖ rem).
  Proof.
    iIntros (?) "HFR Hfr1".

    iDestruct (free_roles_inclusion with "HFR Hfr1") as %Hincl.

    replace FR with ((FR ∖ rem) ∪ rem); last first.
    { rewrite difference_union_L. set_solver. }
    replace fr1 with ((fr1 ∖ rem) ∪ rem); last first.
    { rewrite difference_union_L. set_solver. }

    iAssert (frag_free_roles_are (fr1 ∖ rem) ∗ frag_free_roles_are rem)%I with "[Hfr1]" as "[Hfr2 Hrem]".
    { rewrite /frag_free_roles_are -own_op -auth_frag_op gset_disj_union //. set_solver. }

    iCombine "HFR Hrem" as "H".
    iMod (own_update with "H") as "[??]" ; eauto.
    - apply auth_update, gset_disj_dealloc_local_update.
    - iModIntro. iFrame. iApply (own_proper with "Hfr2").
      do 2 f_equiv. set_solver.
  Qed.

  Lemma update_free_roles_strong fr1 fr2 FR'
    (DISJ1: fr1 ## FR') (DISJ2: fr2 ## FR'):
    auth_free_roles_are (fr1 ∪ FR') -∗
    frag_free_roles_are fr1 ==∗
    auth_free_roles_are (fr2 ∪ FR') ∗
    frag_free_roles_are fr2.
  Proof.
    iIntros "HFR Hfr1".
    iApply own_op. 
    iMod (own_update with "[Hfr1 HFR]") as "?".
    3: { done. }
    2: { iApply own_op. iFrame. }
    apply auth_update.
    etrans.
    { apply gset_disj_dealloc_local_update. }
    rewrite difference_union_distr_l_L difference_diag_L union_empty_l_L.
    rewrite difference_disjoint_L; auto.
    etrans. 
    - by apply gset_disj_alloc_local_update with (Z := fr2).
    - eapply local_update_proper.
      1: rewrite union_empty_r_L.
      all: reflexivity.
  Qed. 

  Lemma model_agree s1 s2:
    auth_model_is s1 -∗ frag_model_is s2 -∗ ⌜ s1 = s2 ⌝.
  Proof.
    iIntros "Ha Hf".
    by iDestruct (own_valid_2 with "Ha Hf") as
      %[Heq%Excl_included%leibniz_equiv ?]%auth_both_valid_discrete.
  Qed.

  Lemma model_agree' δ1 s2:
    model_state_interp δ1 -∗ frag_model_is s2 -∗ ⌜ ls_under δ1 = s2 ⌝.
  Proof.
    iIntros "Hsi Hs2". iDestruct "Hsi" as (?) "(_&_&_&Hs1&_)".
    iApply (model_agree with "Hs1 Hs2").
  Qed.

  Lemma update_fuel_delete ρ f F:
    auth_fuel_is F -∗ ρ ↦F f ==∗ auth_fuel_is (delete ρ F).
  Proof.
    iIntros "Hafuel Hfuel".
    iCombine "Hafuel Hfuel" as "H".
    iMod (own_update with "H") as "H"; last first.
    { iModIntro. iFrame. }
    rewrite map_fmap_singleton fmap_delete.
    eapply auth_update_dealloc.
    apply delete_singleton_local_update.
    typeclasses eauto.
  Qed.

  Lemma has_fuel_in ζ δ fs:
    has_fuels ζ fs -∗ model_state_interp δ -∗ ⌜ ∀ ρ, ls_mapping δ !! ρ = Some ζ <-> ρ ∈ dom fs ⌝.
  Proof.
    unfold model_state_interp, has_fuels, auth_mapping_is, frag_mapping_is.
    iIntros "[Hζ Hfuels] (%FR&Hafuel&Hamapping &HFR&Hamod&Hfr) %ρ".
    iCombine "Hamapping Hζ" as "H".
    iDestruct (own_valid with "H") as %Hval. iPureIntro.
    apply auth_both_valid_discrete in Hval as [Hval ?].
    rewrite map_fmap_singleton in Hval.
    apply singleton_included_exclusive_l in Hval =>//; last by typeclasses eauto.
    rewrite -> lookup_fmap, leibniz_equiv_iff in Hval.
    apply fmap_Some_1 in Hval as (R'&HMζ&?). simplify_eq.
    pose proof (ls_mapping_tmap_corr δ (LM := LM)) as Hmapinv. 
    rewrite (Hmapinv ρ ζ) HMζ. split.
    - intros (?&?&?). by simplify_eq.
    - intros ?. eexists. split; eauto.
  Qed.

  Lemma has_fuel_fuel ζ δ fs:
    has_fuels ζ fs -∗ model_state_interp δ -∗ 
    ⌜ ∀ ρ, ρ ∈ dom fs -> ls_fuel δ !! ρ = fs !! ρ ⌝.
  Proof.
    unfold has_fuels, model_state_interp, auth_fuel_is.
    iIntros "[Hζ Hfuels] (%FR&Hafuel&Hamapping&HFR&Hamod)" (ρ Hρ).
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

  Lemma frag_free_roles_fuels_disj: forall δ fr fs tid,
        model_state_interp δ -∗ frag_free_roles_are fr -∗ 
        has_fuels tid fs (PMPP := ActualOwnershipPartialPre) -∗
        ⌜ fr ## dom fs⌝. 
  Proof using. 
    iIntros (????) "MSI FREE FUELS". 
    rewrite /model_state_interp.
    iAssert (⌜ dom fs ⊆ dom (ls_fuel δ) ⌝)%I as "%INCL2".
    { iDestruct (has_fuel_fuel with "FUELS MSI") as "%IN".
      iPureIntro. apply elem_of_subseteq.
      intros ? DOM. specialize (IN _ DOM).
      apply elem_of_dom. rewrite IN. by apply elem_of_dom.  }
    iDestruct "MSI" as (?) "(?&?&FREE'&?&%DISJ)".
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

  Definition update_fuel_resource 
    (δ1: LiveState Λ M) (fs1 fs2: gmap (fmrole M) nat) (s2: M): gmap (fmrole M) nat :=
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

End model_state_lemmas.

Section adequacy.
  Context `{LM: LiveModel Λ M}.
  Context `{Countable (locale Λ)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGpreS LM Σ}.

  Lemma model_state_init (s0: M):
    ⊢ |==> ∃ γ,
        own (A := authUR (optionUR (exclR (ModelO M)))) γ
            (● (Excl' s0) ⋅ ◯ (Excl' s0)).
  Proof.
    iMod (own_alloc (● Excl' s0 ⋅ ◯ Excl' s0)) as (γ) "[Hfl Hfr]".
    { by apply auth_both_valid_2. }
    iExists _. by iSplitL "Hfl".
  Qed.

  Lemma model_mapping_init (s0: M) (ζ0: locale Λ):
    ⊢ |==> ∃ γ,
        own (A := authUR (gmapUR _ (exclR (gsetR (RoleO M))))) γ
            (● ({[ ζ0 :=  Excl (M.(live_roles) s0) ]}) ⋅
               ◯ ({[ ζ0 :=  Excl (M.(live_roles) s0) ]})).  
  Proof.
    iMod (own_alloc (● ({[ ζ0 :=  Excl (M.(live_roles) s0) ]}) ⋅
                       ◯ ({[ ζ0 :=  Excl (M.(live_roles) s0) ]}): authUR (gmapUR _ _))) as (γ) "[Hfl Hfr]".
    { apply auth_both_valid_2; eauto. by apply singleton_valid. }
    iExists _. by iSplitL "Hfl".
  Qed.

  Lemma model_fuel_init (s0: M):
    ⊢ |==> ∃ γ,
        own (A := authUR (gmapUR (RoleO M) (exclR natO))) γ
            (● gset_to_gmap (Excl (LM.(lm_fl) s0)) (M.(live_roles) s0)  ⋅
               (◯ gset_to_gmap (Excl (LM.(lm_fl) s0)) (M.(live_roles) s0))).
  Proof.
    iMod (own_alloc
            (● gset_to_gmap (Excl (LM.(lm_fl) s0)) (M.(live_roles) s0)  ⋅
               (◯ gset_to_gmap (Excl (LM.(lm_fl) s0)) (M.(live_roles) s0)))) as (γ) "[H1 H2]".
    { apply auth_both_valid_2;eauto. intros ρ.
      destruct (gset_to_gmap (Excl (LM.(lm_fl) s0)) (live_roles M s0) !! ρ) eqn:Heq;
        rewrite Heq; last done.
      apply lookup_gset_to_gmap_Some in Heq.
      destruct Heq as [?<-]. done. }
    iExists _. by iSplitL "H1".
  Qed.

  Lemma model_free_roles_init (s0: M) (FR: gset _):
    ⊢ |==> ∃ γ,
        own (A := authUR (gset_disjUR (RoleO M))) γ (● GSet FR  ⋅ ◯ GSet FR).
  Proof.
    iMod (own_alloc (● GSet FR  ⋅ ◯ GSet FR)) as (γ) "[H1 H2]".
    { apply auth_both_valid_2 =>//. }
    iExists _. by iSplitL "H1".
  Qed.
End adequacy.
