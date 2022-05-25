From trillium.fairness Require Import fairness.
From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.


Canonical Structure ModelO (Mdl : FairModel) := leibnizO Mdl.
Canonical Structure RoleO (Mdl : FairModel) := leibnizO (Mdl.(fmrole)).
Canonical Structure localeO (Λ : language) := leibnizO (locale Λ).

Class fairnessGpreS (Mdl : FairModel) Λ Σ `{Countable (locale Λ)} := {
  fairnessGpreS_model :> inG Σ (authUR (optionUR (exclR (ModelO Mdl))));
  fairnessGpreS_model_mapping :> inG Σ (authUR (gmapUR (localeO Λ) (exclR (gsetR (RoleO Mdl)))));
  fairnessGpreS_model_fuel :> inG Σ (authUR (gmapUR (RoleO Mdl) (exclR natO)));
}.

Class fairnessGS (Mdl: FairModel) Λ Σ `{Countable (locale Λ)} := FairnessGS {
  fairness_inG :> fairnessGpreS Mdl Λ Σ;
  (** Underlying model *)
  fairness_model_name : gname;
  (** Mapping of threads to sets of roles *)
  fairness_model_mapping_name : gname;
  (** Mapping of roles to fuel *)
  fairness_model_fuel_name : gname;
}.

Global Arguments FairnessGS Mdl Λ  Σ {_ _ _} _ _ _.
Global Arguments fairness_model_name {Mdl Λ Σ _ _} _.
Global Arguments fairness_model_mapping_name {Mdl Λ Σ _ _} _ : assert.
Global Arguments fairness_model_fuel_name {Mdl Λ Σ _ _} _ : assert.

Definition fairnessΣ (Mdl: FairModel) Λ `{Countable (locale Λ)} : gFunctors := #[
   GFunctor (authUR (optionUR (exclR (ModelO Mdl))));
   GFunctor (authUR (gmapUR (localeO Λ) (exclR (gsetR (RoleO Mdl)))));
   GFunctor (authUR (gmapUR (RoleO Mdl) (exclR natO)))
].

Global Instance subG_fairnessGpreS {Σ Λ Mdl} `{Countable (locale Λ)} :
  subG (fairnessΣ Mdl Λ) Σ -> fairnessGpreS Mdl Λ Σ.
Proof. solve_inG. Qed.

Notation "f ⇂ R" := (filter (λ '(k,v), k ∈ R) f) (at level 30).

Lemma dom_domain_restrict `{Countable X} {A} (f: gmap X A) (R: gset X):
  R ⊆ dom f ->
  dom  (f ⇂ R) = R.
Proof.
  intros ?. apply dom_filter_L.
  intros i; split; [|set_solver].
  intros Hin. assert (Hin': i ∈ dom f) by set_solver.
  apply elem_of_dom in Hin' as [??]. set_solver.
Qed.

Lemma dom_domain_restrict_union_l `{Countable X} {A} (f: gmap X A) R1 R2:
  R1 ∪ R2 ⊆ dom f ->
  dom (f ⇂ R1) = R1.
Proof.
  intros ?. apply dom_domain_restrict. set_solver.
Qed.
Lemma dom_domain_restrict_union_r `{Countable X} {A} (f: gmap X A) R1 R2:
  R1 ∪ R2 ⊆ dom f ->
  dom (f ⇂ R2) = R2.
Proof.
  intros ?. apply dom_domain_restrict. set_solver.
Qed.

Section bigop_utils.
  Context `{Monoid M o}.
  Context `{Countable K}.

  Lemma big_opMS (g: gset K) (P: K -> M):
    ([^ o set] x ∈ g, P x) ≡ [^ o map] x ↦ y ∈ (mapset_car g), P x.
  Proof.
    rewrite big_opS_elements /elements /gset_elements /mapset_elements.
    rewrite big_opM_map_to_list.
    destruct g as [g]. simpl. rewrite big_opL_fmap.
    f_equiv.
  Qed.
End bigop_utils.

Section bigop_utils.
  Context `{Countable K} {A : cmra}.
  Implicit Types m : gmap K A.
  Implicit Types i : K.

  Lemma gset_to_gmap_singletons (a : A) (g : gset K):
    ([^op set] x ∈ g, {[x := a]}) ≡ gset_to_gmap a g.
  Proof.
    rewrite big_opMS.
    rewrite -(big_opM_singletons (gset_to_gmap a g)).
    rewrite /gset_to_gmap big_opM_fmap //.
  Qed.
End bigop_utils.

Section map_utils.
  Context `{Countable K, Countable V, EqDecision K}.

  Definition maps_inverse_match (m: gmap K V) (m': gmap V (gset K)) :=
    ∀ (k: K) (v: V), m !! k = Some v <-> ∃ (ks: gset K), m' !! v = Some ks ∧ k ∈ ks.

  Lemma no_locale_empty M M' ρ ζ:
    maps_inverse_match M M' ->
    M' !! ζ = Some ∅ ->
    M !! ρ ≠ Some ζ.
  Proof.
    intros Hinv Hem contra.
    destruct (Hinv ρ ζ) as [Hc _]. destruct (Hc contra) as (?&?&?).
    by simplify_eq.
  Qed.

  Lemma maps_inverse_bij M M' ρ X1 X2 ζ ζ':
    maps_inverse_match M M' ->
    M' !! ζ = Some X1 -> ρ ∈ X1 ->
    M' !! ζ' = Some X2 -> ρ ∈ X2 ->
    ζ = ζ'.
  Proof.
    intros Hinv Hζ Hρ Hζ' Hρ'.
    assert (M !! ρ = Some ζ); first by apply Hinv; eexists; done.
    assert (M !! ρ = Some ζ'); first by apply Hinv; eexists; done.
    congruence.
  Qed.

End map_utils.

Section fin_map_dom.
Context `{FinMapDom K M D}.
Lemma dom_empty_iff {A} (m : M A) : dom m ≡ ∅ ↔ m = ∅.
Proof.
  split; [|intros ->; by rewrite dom_empty].
  intros E. apply map_empty. intros. apply not_elem_of_dom.
  rewrite E. set_solver.
Qed.

Section leibniz.
  Context `{!LeibnizEquiv D}.
  Lemma dom_empty_iff_L {A} (m : M A) : dom m = ∅ ↔ m = ∅.
  Proof. unfold_leibniz. apply dom_empty_iff. Qed.
End leibniz.
End fin_map_dom.

Section map_imap.
  Context `{Countable K}.
  Lemma map_imap_dom_inclusion {A B} (f : K → A → option B) (m : gmap K A) :
    dom (map_imap f m) ⊆ dom m.
  Proof.
    intros i [k Hk]%elem_of_dom. rewrite map_lookup_imap in Hk.
    destruct (m !! i) eqn:?; last done.
    rewrite elem_of_dom. by eexists.
  Qed.
  Lemma map_imap_dom_eq {A B} (f : K → A → option B) (m : gmap K A) :
    (forall k a, k ∈ dom m -> is_Some (f k a)) ->
    dom (map_imap f m) = dom m.
  Proof.
    rewrite -leibniz_equiv_iff. intros HisSome i. split.
    - intros [x Hx]%elem_of_dom. rewrite map_lookup_imap in Hx.
      apply elem_of_dom. destruct (m !! i) eqn:Heq; eauto.
      by simpl in Hx.
    - intros [x Hx]%elem_of_dom.
      rewrite elem_of_dom map_lookup_imap Hx /=. apply HisSome, elem_of_dom. eauto.
  Qed.
End map_imap.

Section locales_utils.
  Context {Λ: language}.

  Definition locales_of_list_from tp0 (tp: list $ expr Λ): list $ locale Λ :=
    (λ '(t, e), locale_of t e) <$> (prefixes_from tp0 tp).
  Notation locales_of_list tp := (locales_of_list_from [] tp).

  Lemma locales_of_list_equiv tp0 tp0' tp1 tp2:
    locales_equiv_from tp0 tp0' tp1 tp2 →
    locales_of_list_from tp0 tp1 = locales_of_list_from tp0' tp2.
  Proof.
    revert tp0 tp0' tp1. induction tp2; intros tp0 tp0' tp1 H;
    destruct tp1 as [|e1 tp1]; try by apply Forall2_length in H.
    unfold locales_of_list_from. simpl.
    simpl in H. apply Forall2_cons_1 in H as [??]. f_equal =>//.
    apply IHtp2 =>//.
  Qed.

  Lemma locales_of_list_step_incl σ1 σ2 oζ tp1 tp2 :
      locale_step (tp1, σ1) oζ (tp2, σ2) ->
      locales_of_list tp1 ⊆ locales_of_list tp2.
  Proof.
    intros H. inversion H; simplify_eq=>//.
    replace (t1 ++ e2 :: t2 ++ efs) with ((t1 ++ e2 :: t2) ++ efs); last by list_simplifier.
    rewrite /locales_of_list_from. rewrite [in X in _ ⊆ X]prefixes_from_app /= fmap_app.
    assert ((λ '(t, e), locale_of t e) <$> prefixes (t1 ++ e1 :: t2) = (λ '(t, e), locale_of t e) <$> prefixes (t1 ++ e2 :: t2))
      as ->; last set_solver.
    apply locales_of_list_equiv, locales_equiv_middle. by eapply locale_step_preserve.
  Qed.

  Lemma locales_of_list_from_locale_from `{EqDecision (locale Λ)} tp0 tp1 ζ:
    is_Some (from_locale_from tp0 tp1 ζ) ->
    ζ ∈ locales_of_list_from tp0 tp1.
  Proof.
    revert tp0; induction tp1 as [|e1 tp1 IH]; intros tp0.
    { simpl. intros H. inversion H. congruence. }
    simpl. intros [e Hsome]. rewrite /locales_of_list_from /=.
    destruct (decide (locale_of tp0 e1 = ζ)); simplify_eq; first set_solver.
    apply elem_of_cons; right. apply IH. eauto.
  Qed.

End locales_utils.
Notation locales_of_list tp := (locales_of_list_from [] tp).

Section model_state_interp.
  Context {Mdl: FairModel}.
  Context `{fG: fairnessGS Mdl Λ Σ}.

  Notation Role := (Mdl.(fmrole)).

  Definition auth_fuel_is (F: gmap Role nat): iProp Σ :=
    own (fairness_model_fuel_name fG)
        (● (fmap (λ f, Excl f) F : ucmra_car (gmapUR (RoleO Mdl) (exclR natO)))).

  Definition frag_fuel_is (F: gmap Role nat): iProp Σ :=
    own (fairness_model_fuel_name fG)
        (◯ (fmap (λ f, Excl f) F : ucmra_car (gmapUR (RoleO Mdl) (exclR natO)))).

  Definition auth_mapping_is (M: gmap (locale Λ) (gset Role)): iProp Σ :=
    own (fairness_model_mapping_name fG)
        (● ( (fmap (λ (f: gset Mdl.(fmrole)), Excl f) M) :
              ucmra_car (gmapUR _ (exclR (gsetR (RoleO Mdl))))
        )).

  Definition frag_mapping_is (M: gmap (locale Λ) (gset Role)): iProp Σ :=
    own (fairness_model_mapping_name fG)
        (◯ ( (fmap (λ (f: gset Mdl.(fmrole)), Excl f) M) :
              ucmra_car (gmapUR _ (exclR (gsetR (RoleO Mdl))))
        )).

  Definition auth_model_is (M: Mdl): iProp Σ :=
    own (fairness_model_name fG) (● Excl' M).

  Definition frag_model_is (M: Mdl): iProp Σ :=
    own (fairness_model_name fG) (◯ Excl' M).

  Definition model_state_interp (tp: list $ expr Λ) (δ: LiveState Mdl): iProp Σ :=
    ∃ M, auth_fuel_is δ.(ls_fuel) ∗
      auth_mapping_is M ∗ ⌜maps_inverse_match δ.(ls_mapping) M⌝ ∗
      ⌜ ∀ ζ, ζ ∉ locales_of_list tp → M !! ζ = None ⌝ ∗
      auth_model_is δ.

  Lemma model_state_interp_tids_smaller δ tp :
    model_state_interp tp δ -∗ ⌜ tids_smaller tp δ ⌝.
  Proof.
    iIntros "(%M&_&_&%Hminv&%Hbig&_)". iPureIntro.
    intros ρ ζ Hin.
    assert (¬ (ζ ∉ locales_of_list tp)).
    - intros contra.
      apply Hminv in Hin as [? [Hsome _]].
      specialize (Hbig _ contra); congruence.
    - destruct (decide (ζ ∈ locales_of_list tp)) as [Hin'|] =>//.
      apply elem_of_list_fmap in Hin' as [[tp' e'] [-> Hin']].
      unfold from_locale. exists e'. by apply from_locale_from_Some.
  Qed.
End model_state_interp.

Lemma own_proper `{inG Σ X} γ (x y: X):
  x ≡ y ->
  own γ x -∗ own γ y.
Proof. by intros ->. Qed.

Lemma auth_fuel_is_proper `{fairnessGS Mdl Λ Σ} (x y : gmap (fmrole Mdl) nat):
  x = y ->
  auth_fuel_is x -∗ auth_fuel_is y.
Proof. by intros ->. Qed.

Notation "tid ↦M R" := (frag_mapping_is {[ tid := R ]}) (at level 33).
Notation "tid ↦m ρ" := (frag_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
Notation "ρ ↦F f" := (frag_fuel_is {[ ρ := f ]}) (at level 33).

Section model_state_lemmas.
  Context {Mdl: FairModel}.
  Context `{fairnessGS Mdl Λ Σ}.

  Notation Role := (Mdl.(fmrole)).

  Definition has_fuel (ζ: locale Λ) (ρ: Role) (f: nat): iProp Σ :=
    ζ ↦m ρ ∗ ρ ↦F f.

  Definition has_fuels (ζ: locale Λ) (fs: gmap Role nat): iProp Σ :=
    ζ ↦M dom fs ∗ [∗ set] ρ ∈ dom fs, ∃ f, ⌜fs !! ρ = Some f⌝ ∧ ρ ↦F f.

  #[global] Instance has_fuels_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (has_fuels).
  Proof. solve_proper. Qed.

  #[global] Instance has_fuels_timeless (ζ: locale Λ) (fs: gmap Role nat):
    Timeless (has_fuels ζ fs).
  Proof. rewrite /has_fuels. apply _. Qed.

  Lemma has_fuel_fuels (ζ: locale Λ) (ρ: Role) (f: nat):
    has_fuel ζ ρ f ⊣⊢ has_fuels ζ {[ ρ := f ]}.
  Proof.
    rewrite /has_fuel /has_fuels. iSplit.
    - iIntros "[Hζ Hρ]". rewrite dom_singleton_L big_sepS_singleton. iFrame.
      iExists f. iFrame. iPureIntro. by rewrite lookup_singleton.
    - iIntros "(?&H)". rewrite dom_singleton_L big_sepS_singleton. iFrame.
      iDestruct "H" as (?) "H". rewrite lookup_singleton.
      iDestruct "H" as "[% ?]". by simplify_eq.
  Qed.

  Definition has_fuels_S (ζ: locale Λ) (fs: gmap Role nat): iProp Σ :=
    has_fuels ζ (fmap S fs).

  Definition has_fuels_plus (n: nat) (ζ: locale Λ) (fs: gmap Role nat): iProp Σ :=
    has_fuels ζ (fmap (fun m => n+m) fs).

  Lemma has_fuel_fuels_S (ζ: locale Λ) (ρ: Role) (f: nat):
    has_fuel ζ ρ (S f) ⊣⊢ has_fuels_S ζ {[ ρ := f ]}.
  Proof.
    rewrite has_fuel_fuels /has_fuels_S map_fmap_singleton //.
  Qed.

  Lemma has_fuel_fuels_plus_1 (ζ: locale Λ) fs:
    has_fuels_plus 1 ζ fs ⊣⊢ has_fuels_S ζ fs.
  Proof.
    rewrite /has_fuels_plus /has_fuels_S. do 2 f_equiv.
    intros m m' ->. apply leibniz_equiv_iff. lia.
  Qed.

  Lemma has_fuel_fuels_plus_0 (ζ: locale Λ) fs:
    has_fuels_plus 0 ζ fs ⊣⊢ has_fuels ζ fs.
  Proof.
    rewrite /has_fuels_plus /=.  f_equiv. intros ?.
    rewrite lookup_fmap. apply leibniz_equiv_iff.
    destruct (fs !! i) eqn:Heq; rewrite Heq //.
  Qed.

  Lemma has_fuels_plus_split_S n (ζ: locale Λ) fs:
    has_fuels_plus (S n) ζ fs ⊣⊢ has_fuels_S ζ ((λ m, n + m) <$> fs).
  Proof.
    rewrite /has_fuels_plus /has_fuels_S. f_equiv.
    rewrite -map_fmap_compose /= => ρ.
    rewrite !lookup_fmap //.
  Qed.

  Lemma frag_mapping_same ζ M R:
    auth_mapping_is M -∗ ζ ↦M R -∗ ⌜ M !! ζ = Some R ⌝.
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

End model_state_lemmas.

Section adequacy.

  Lemma model_state_init `{fairnessGpreS Mdl Λ Σ} (s0: Mdl):
    ⊢ |==> ∃ γ,
        own (A := authUR (optionUR (exclR (ModelO Mdl)))) γ
            (● (Excl' s0) ⋅ ◯ (Excl' s0)).
  Proof.
    iMod (own_alloc (● Excl' s0 ⋅ ◯ Excl' s0)) as (γ) "[Hfl Hfr]".
    { by apply auth_both_valid_2. }
    iExists _. by iSplitL "Hfl".
  Qed.

  Lemma model_mapping_init `{fairnessGpreS Mdl Λ Σ} (s0: Mdl) (ζ0: locale Λ):
    ⊢ |==> ∃ γ,
        own (A := authUR (gmapUR _ (exclR (gsetR (RoleO Mdl))))) γ
            (● ({[ ζ0 :=  Excl (Mdl.(live_roles) s0) ]}) ⋅
               ◯ ({[ ζ0 :=  Excl (Mdl.(live_roles) s0) ]})).
  Proof.
    iMod (own_alloc (● ({[ ζ0 :=  Excl (Mdl.(live_roles) s0) ]}) ⋅
                       ◯ ({[ ζ0 :=  Excl (Mdl.(live_roles) s0) ]}))) as (γ) "[Hfl Hfr]".
    { apply auth_both_valid_2; eauto. by apply singleton_valid. }
    iExists _. by iSplitL "Hfl".
  Qed.

  Lemma model_fuel_init `{fairnessGpreS Mdl Λ Σ} (s0: Mdl):
    ⊢ |==> ∃ γ,
        own (A := authUR (gmapUR (RoleO Mdl) (exclR natO))) γ
            (● gset_to_gmap (Excl (fuel_limit s0)) (Mdl.(live_roles) s0)  ⋅
               (◯ gset_to_gmap (Excl (fuel_limit s0)) (Mdl.(live_roles) s0))).
  Proof.
    iMod (own_alloc
            (● gset_to_gmap (Excl (fuel_limit s0)) (Mdl.(live_roles) s0)  ⋅
               (◯ gset_to_gmap (Excl (fuel_limit s0)) (Mdl.(live_roles) s0)))) as (γ) "[H1 H2]".
    { apply auth_both_valid_2;eauto. intros ρ.
      destruct (gset_to_gmap (Excl (fuel_limit s0)) (live_roles Mdl s0) !! ρ) eqn:Heq;
        rewrite Heq; last done.
      apply lookup_gset_to_gmap_Some in Heq.
      destruct Heq as [?<-]. done. }
    iExists _. by iSplitL "H1".
  Qed.

End adequacy.

Section model_state_lemmas.
  Context {Mdl: FairModel}.
  Context `{fairnessGS Mdl Λ Σ}.
  Context `{EqDecision (expr Λ)}.

  Lemma update_model δ δ1 δ2:
    auth_model_is δ1 -∗ frag_model_is δ2 ==∗ auth_model_is δ ∗ frag_model_is δ.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "[??]" ; eauto.
    - by apply auth_update, option_local_update, (exclusive_local_update _ (Excl δ)).
    - iModIntro. iFrame.
  Qed.

  Lemma model_agree s1 s2:
    auth_model_is s1 -∗ frag_model_is s2 -∗ ⌜ s1 = s2 ⌝.
  Proof.
    iIntros "Ha Hf".
      by iDestruct (own_valid_2 with "Ha Hf") as
          %[Heq%Excl_included%leibniz_equiv ?]%auth_both_valid_discrete.
  Qed.

  Lemma model_agree' δ1 s2 n:
    model_state_interp n δ1 -∗ frag_model_is s2 -∗ ⌜ ls_under δ1 = s2 ⌝.
  Proof.
    iIntros "Hsi Hs2". iDestruct "Hsi" as (?) "(_&_&_&_&Hs1)".
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

  Definition fuel_apply (fs' F:  gmap (fmrole Mdl) nat) (LR: gset (fmrole Mdl)):
    gmap (fmrole Mdl) nat :=
    map_imap
      (λ (ρ: fmrole Mdl ) (fold : nat),
       match decide (ρ ∈ dom fs') with
       | left x => fs' !! ρ
       | right _ => F !! ρ
       end) (gset_to_gmap (0%nat) LR).

  Definition update_fuel_resource (δ1: LiveState Mdl) (fs2: gmap (fmrole Mdl) nat) (s2: Mdl):
    gmap (fmrole Mdl) nat :=
    fuel_apply fs2 (δ1.(ls_fuel (Λ := Λ))) (live_roles _ s2).

  Lemma elem_of_frame_excl_map
        (fs F: gmap (fmrole Mdl) nat)
        (mf: gmap (fmrole Mdl) (excl nat))
        (ρ: fmrole Mdl)
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

  Lemma update_mapping ζ (R' : gset $ fmrole Mdl) (R: gset (fmrole Mdl)) M:
    auth_mapping_is M -∗ ζ ↦M R ==∗ auth_mapping_is (<[ ζ := R' ]> M) ∗ ζ ↦M R'.
  Proof.
    iIntros "Hamap Hmap".
    iCombine "Hamap Hmap" as "H".
    iMod (own_update with "H") as "[A B]"; last first.
    { iModIntro. iSplitL "A"; iFrame. }
    rewrite !map_fmap_singleton fmap_insert.
    eapply auth_update, singleton_local_update_any.
    intros. by apply exclusive_local_update.
  Qed.

  Lemma mapping_lookup ζ M R:
    auth_mapping_is M -∗ ζ ↦M R -∗ ⌜ ζ ∈ dom M ⌝.
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

  Lemma update_mapping_new_locale ζ ζ' (R R1 R2 : gset $ fmrole Mdl) M:
    ζ' ∉ dom M ->
    auth_mapping_is M -∗
                         ζ ↦M R ==∗
                                      auth_mapping_is (<[ ζ' := R2]> (<[ ζ := R1 ]> M)) ∗
                                      ζ ↦M R1 ∗ ζ' ↦M R2.
  Proof.
    iIntros (Hnotin) "Hamap Hmap".
    iDestruct (mapping_lookup with "Hamap Hmap") as %Hin.
    iCombine "Hamap Hmap" as "H".
    iMod (own_update (A := (authUR (gmapUR _ (exclR (gsetR (RoleO Mdl)))))) _ _ (
                       ● ((λ f : gset (fmrole Mdl), Excl f) <$> ((<[ ζ := R1 ]> M)))
                         ⋅ ◯ ((λ f : gset (fmrole Mdl), Excl f) <$> {[ζ := R1]})
                     ) with "H") as "[A B]".
    { rewrite !map_fmap_singleton fmap_insert.
      eapply auth_update. eapply singleton_local_update_any.
      intros. by apply exclusive_local_update. }
    iCombine "A B" as "H".
    iMod (own_update (A := (authUR (gmapUR _ (exclR (gsetR (RoleO Mdl)))))) _ _ (
                       ● ((λ f : gset (fmrole Mdl), Excl f) <$> (<[ ζ' := R2]> (<[ ζ := R1 ]> M)))
                         ⋅ ◯ ((λ f : gset (fmrole Mdl), Excl f) <$> {[ζ := R1 ; ζ' := R2]})
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

  Lemma update_mapping_delete ζ (Rrem : gset $ fmrole Mdl) (R: gset (fmrole Mdl)) M:
    auth_mapping_is M -∗ ζ ↦M R ==∗ auth_mapping_is (<[ ζ := R ∖ Rrem ]> M) ∗ ζ ↦M (R ∖ Rrem).
  Proof.
    eauto using update_mapping.
  Qed.

  Lemma update_mapping_add ζ (Radd : gset $ fmrole Mdl) (R: gset (fmrole Mdl)) M:
    auth_mapping_is M -∗ ζ ↦M R ==∗ auth_mapping_is (<[ ζ := R ∪ Radd ]> M) ∗ ζ ↦M (R ∪ Radd).
  Proof.
    eauto using update_mapping.
  Qed.

  Lemma has_fuels_equiv fs ζ:
    has_fuels ζ fs ⊣⊢ ζ ↦M (dom fs) ∗ ([∗ map] ρ ↦ f ∈ fs, ρ ↦F f).
  Proof.
    rewrite /has_fuels -big_opM_dom. iSplit.
    - iIntros "($ & H)". iApply (big_sepM_impl with "H").
      iIntros "!#" (ρ f Hin) "(%f' & %Hin' & ?)".
        by simplify_eq.
    - iIntros "($&H)".
      iApply (big_sepM_impl with "H").
      iIntros "!#" (ρ f Hin)  "?". iExists f. iSplit; done.
  Qed.

  Lemma update_has_fuels ζ fs fs' F M:
    let LR := (dom F ∪ dom fs') ∖ (dom fs ∖ dom fs') in
    (fs ≠ ∅) ->
    (dom fs' ∖ dom fs ∩ dom F = ∅) ->
    has_fuels ζ fs -∗
    auth_fuel_is F -∗
    auth_mapping_is M ==∗
      auth_fuel_is (fuel_apply fs' F LR) ∗
      has_fuels ζ fs' ∗
      auth_mapping_is (<[ ζ := dom fs' ]> M).
  Proof.
    iIntros (LR Hfs Hdom) "Hfuels Hafuels Hamapping".
    rewrite !has_fuels_equiv. iDestruct "Hfuels" as "[Hmapping Hfuels]".
    iMod (update_fuel with "Hafuels Hfuels") as "[Hafuels Hfuels]" =>//.
    iMod (update_mapping with "Hamapping Hmapping") as "[Hamapping Hmapping]".
    iModIntro.
    iFrame.
  Qed.

  Lemma update_has_fuels_no_step ζ fs fs' F M:
    let LR := (dom F ∪ dom fs') ∖ (dom fs ∖ dom fs') in
    (fs ≠ ∅) ->
    (dom fs' = dom fs) ->
    has_fuels ζ fs -∗
    auth_fuel_is F -∗
    auth_mapping_is M ==∗
      auth_fuel_is (fuel_apply fs' F LR) ∗
      has_fuels ζ fs' ∗
      auth_mapping_is M.
  Proof.
    iIntros (LR Hfs Hdom) "Hfuels Hafuels Hamapping".
    rewrite !has_fuels_equiv. iDestruct "Hfuels" as "[Hmapping Hfuels]".
    iMod (update_fuel fs fs' with "Hafuels Hfuels") as "[Hafuels Hfuels]" =>//.
    { rewrite Hdom. set_solver. }
    iModIntro.
    iFrame. rewrite Hdom //.
  Qed.

  Lemma has_fuel_in ζ δ fs n:
    has_fuels ζ fs -∗ model_state_interp n δ -∗ ⌜ ∀ ρ, ls_mapping δ !! ρ = Some ζ <-> ρ ∈ dom fs ⌝.
  Proof.
    unfold model_state_interp, has_fuels, auth_mapping_is, frag_mapping_is.
    iIntros "[Hζ Hfuels] (%M&Hafuel&Hamapping&%Hmapinv&Hamod) %ρ".
    iCombine "Hamapping Hζ" as "H".
    iDestruct (own_valid with "H") as %Hval. iPureIntro.
    apply auth_both_valid_discrete in Hval as [Hval ?].
    rewrite map_fmap_singleton in Hval.
    apply singleton_included_exclusive_l in Hval =>//; last by typeclasses eauto.
    rewrite -> lookup_fmap, leibniz_equiv_iff in Hval.
    apply fmap_Some_1 in Hval as (R'&HMζ&?). simplify_eq.
    rewrite (Hmapinv ρ ζ) HMζ. split.
    - intros (?&?&?). congruence.
    - intros ?. eexists. split; eauto.
  Qed.

  Lemma has_fuel_fuel ζ δ fs n:
    has_fuels ζ fs -∗ model_state_interp n δ -∗  ⌜ ∀ ρ, ρ ∈ dom fs -> ls_fuel δ !! ρ = fs !! ρ ⌝.
  Proof.
    unfold has_fuels, model_state_interp, auth_fuel_is.
    iIntros "[Hζ Hfuels] (%M&Hafuel&Hamapping&%Hmapinv&Hamod)" (ρ Hρ).
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

  Lemma update_no_step_enough_fuel extr (auxtr : auxiliary_trace (fair_model Mdl)) c2 fs ζ:
    (dom fs ≠ ∅) ->
    locale_step (trace_last extr) (Some ζ) c2 ->
    has_fuels_S ζ fs -∗ model_state_interp (trace_last extr).1 (trace_last auxtr)
    ==∗ ∃ δ2 (ℓ : mlabel $ fair_model Mdl),
        ⌜labels_match (Some ζ) ℓ
        ∧ valid_state_evolution_fairness (extr :tr[Some ζ]: c2) (auxtr :tr[ℓ]: δ2)⌝
                                ∗ has_fuels ζ fs ∗ model_state_interp c2.1 δ2.
  Proof.
    iIntros "%HnotO %Hstep Hf Hmod".
    destruct c2 as [tp2 σ2].
    destruct (set_choose_L _ HnotO) as [??].
    iDestruct (has_fuel_in with "Hf Hmod") as %Hxdom; eauto.
    iDestruct (has_fuel_fuel with "Hf Hmod") as "%Hfuel"; eauto.
    iDestruct (model_state_interp_tids_smaller with "Hmod") as %Hζs.
    iDestruct "Hmod" as "(%M & Hfuel & Hamapping & %Hminv & %Hlocssmall & Hmodel)".
    unfold has_fuels_S.
    simpl in *.

    iMod (update_has_fuels_no_step ζ (S <$> fs) fs with "[Hf] [Hfuel] [Hamapping]") as "(Hafuels&Hfuels&Hamapping)" =>//.
    { rewrite -dom_empty_iff_L. set_solver. }
    { set_solver. }
    iModIntro.
    assert (Hfueldom: dom (fuel_apply fs (ls_fuel (trace_last auxtr))
                                      ((dom (ls_fuel (trace_last auxtr)) ∪ dom fs) ∖ (dom fs ∖ dom fs))) =
                      live_roles Mdl (trace_last auxtr)).
    { unfold fuel_apply.
      assert (dom fs ⊆ live_roles Mdl (trace_last auxtr)).
      { intros ρ Hin. rewrite -ls_fuel_dom elem_of_dom Hfuel; last set_solver.
        apply elem_of_dom in Hin as [? Hin]. rewrite lookup_fmap Hin //=. }
      rewrite (ls_fuel_dom (trace_last auxtr)) map_imap_dom_eq.
      + rewrite dom_gset_to_gmap. set_solver.
      + intros ρ _ Hin. rewrite dom_gset_to_gmap in Hin.
        destruct (decide (ρ ∈ dom fs)) as [Hin'|_].
        * by apply elem_of_dom.
        * apply elem_of_dom. rewrite ls_fuel_dom. set_solver. }
    assert (Hmappingdom: dom (ls_mapping (trace_last auxtr)) = live_roles _ (trace_last auxtr)).
    { apply ls_mapping_dom. }
    iExists {|
      ls_under := (trace_last auxtr).(ls_under);
      ls_fuel := _;
      ls_fuel_dom := Hfueldom;
      ls_mapping := (trace_last auxtr).(ls_mapping);
      ls_mapping_dom := Hmappingdom;
    |}.
    iExists (Silent_step ζ). simpl.
    iSplit; last first.
    { rewrite (dom_fmap_L _ fs). iFrame "Hfuels". iExists M. rewrite /maps_inverse_match //=. iFrame.
      iPureIntro. split; first set_solver.
      unfold tids_smaller; simpl. intros ζ0 Hin.
      unfold tids_smaller in Hζs.
      apply Hlocssmall.
      destruct (trace_last extr).
      have ? := locales_of_list_step_incl _ _ _ _ _ Hstep. simpl.
      clear Hfueldom Hmappingdom. set_solver. }
    iSplit =>//. iSplit; first done. iSplit; last first.
    { iPureIntro.
      unfold tids_smaller; simpl. intros ρ ζ0 Hsome.
      specialize (Hζs _ _ Hsome).
      destruct (trace_last extr); eapply from_locale_step =>//. }
    iSplit.
    { iPureIntro. eexists. apply Hxdom. by rewrite dom_fmap. }
    iSplit.
    { unfold fuel_decr. simpl.
      iIntros "!%" (ρ' Hρ'live Hmustdec).
      inversion Hmustdec; simplify_eq.
      have Hin: ρ' ∈ dom (S <$> fs) by set_solver.
      rewrite map_lookup_imap Hfuel // lookup_fmap.
      destruct (S <$> fs !! ρ') as [f|] eqn:Heq; simpl.
      + rewrite decide_True //; last by set_solver.
        destruct (fs!!ρ') as [f'|]=> //=.
        simpl in Heq. injection Heq=>Heq'. rewrite -Heq'.
        rewrite lookup_gset_to_gmap option_guard_True /=; last by set_solver. lia.
      + have: ρ' ∉ dom (S <$> fs).
        { apply not_elem_of_dom. rewrite lookup_fmap //. }
        set_solver. }
    iPureIntro. split=>//. intros ρ' Hin _.
    rewrite map_lookup_imap. rewrite -ls_fuel_dom in Hin.
    apply elem_of_dom in Hin as [f Hf]. rewrite Hf /=.
    destruct (decide (ρ' ∈ dom fs)).
    + rewrite lookup_gset_to_gmap option_guard_True /=; last by set_solver.
      rewrite -Hf Hfuel; last set_solver. rewrite lookup_fmap.
      destruct (fs!!ρ') as [f'|] eqn:Heq'; first (simpl; lia).
      rewrite Hfuel in Hf; last set_solver. rewrite lookup_fmap Heq' // in Hf.
    + assert (ρ' ∈ dom (ls_fuel (trace_last auxtr))).
      { apply elem_of_dom. eexists _; done. }
      rewrite lookup_gset_to_gmap option_guard_True /=; [lia | set_solver].
  Qed.

  Lemma update_fork_split R1 R2 tp1 tp2 fs (extr : execution_trace Λ)
        (auxtr: auxiliary_trace (fair_model Mdl)) ζ efork σ1 σ2 (Hdisj: R1 ## R2):
    fs ≠ ∅ ->
    R1 ∪ R2 = dom fs ->
    trace_last extr = (tp1, σ1) ->
    locale_step (tp1, σ1) (Some ζ) (tp2, σ2) ->
    (∃ tp1', tp2 = tp1' ++ [efork] ∧ length tp1' = length tp1) ->
    has_fuels_S ζ fs -∗ model_state_interp (trace_last extr).1 (trace_last auxtr) ==∗
      ∃ δ2, has_fuels (locale_of tp1 efork) (fs ⇂ R2) ∗ has_fuels ζ (fs ⇂ R1) ∗ model_state_interp tp2 δ2
        ∧ ⌜valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[Silent_step ζ]: δ2)⌝.
  Proof.
    iIntros (Hnemp Hunioneq -> Hstep Htlen) "Hf Hmod".
    unfold has_fuels_S.
    simpl in *.

    iDestruct (has_fuel_fuel with "Hf Hmod") as %Hfuels.

    iDestruct (model_state_interp_tids_smaller with "Hmod") as %Hts.
    iDestruct "Hmod" as (M) "(Haf&Ham&%Hminv&%Hsmall&Hamod)".

    pose Hlocincl := locales_of_list_step_incl _ _ _ _ _ Hstep.

    iMod (update_has_fuels_no_step ζ (S <$> fs) fs with "Hf Haf Ham") as "(Haf&Hf&Ham)".
    { intros contra. apply fmap_empty_inv in contra. set_solver. }
    { rewrite dom_fmap_L //. }

    iDestruct "Hf" as "(Hf & Hfuels)".
    iDestruct (frag_mapping_same with "Ham Hf") as %Hmapping.

    assert (Hnewζ: (locale_of tp1 efork) ∉ dom M).
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

    iMod (update_mapping_new_locale ζ _ _ R1 R2 with "Ham Hf") as "(Ham&HR1&HR2)"; eauto.

    pose δ1 := trace_last auxtr.
    assert (Hfueldom: dom (map_imap
                             (λ ρ o,
                              if decide (ρ ∈ R1 ∪ R2) then Some (o - 1)%nat else Some o)
                             (ls_fuel δ1)) = live_roles Mdl δ1).
    { rewrite map_imap_dom_eq; first rewrite ls_fuel_dom //.
      intros ρ f Hin. destruct (decide (ρ ∈ R1 ∪ R2)); eauto. }
    assert (Hmappingdom: dom (map_imap
                                (λ ρ o,
                                 if decide (ρ ∈ R2) then Some $ locale_of tp1 efork else Some o)
                                (ls_mapping δ1)) = live_roles Mdl δ1).
    { rewrite map_imap_dom_eq; first rewrite ls_mapping_dom //.
      intros ρ f Hin. destruct (decide (ρ ∈ R2)); eauto. }
    iExists {|
      ls_under := δ1.(ls_under);
      ls_fuel :=
        map_imap (λ ρ o, if (decide (ρ ∈ R1 ∪ R2)) then Some (o-1)%nat else Some o) (ls_fuel δ1);
      ls_fuel_dom := Hfueldom;
      ls_mapping :=
        map_imap (λ ρ o, if (decide (ρ ∈ R2)) then Some $ locale_of tp1 efork else Some o) (ls_mapping δ1);
      ls_mapping_dom := Hmappingdom;
    |}.
    iModIntro.
    assert (Hdomincl: dom fs ⊆ dom (ls_fuel δ1)).
    { intros ρ' Hin'. rewrite elem_of_dom Hfuels; last first.
      { rewrite dom_fmap_L //. }
      rewrite lookup_fmap fmap_is_Some. by apply elem_of_dom. }
    rewrite -Hunioneq big_sepS_union //. iDestruct "Hfuels" as "[Hf1 Hf2]".
    iSplitL "Hf2 HR2".
    { unfold has_fuels. rewrite dom_domain_restrict; [|set_solver]. iFrame.
      iApply (big_sepS_impl with "Hf2"). iIntros "!#" (x Hin) "(%f&%&?)".
      iExists _; iFrame. iPureIntro. rewrite map_filter_lookup_Some //. }
    iSplitL "Hf1 HR1".
    { unfold has_fuels. rewrite dom_domain_restrict; [|set_solver]. iFrame.
      iApply (big_sepS_impl with "Hf1"). iIntros "!#" (x Hin) "(%f&%&?)".
      iExists _; iFrame. iPureIntro. rewrite map_filter_lookup_Some //. }
    iSplitL "Ham Haf Hamod".
    { iExists _; simpl. iFrame "Ham Hamod".
      iSplit.
      - iApply (auth_fuel_is_proper with "Haf"). unfold fuel_apply.
        rewrite -leibniz_equiv_iff. intros ρ. rewrite !map_lookup_imap.
        rewrite Hunioneq dom_fmap_L difference_diag_L difference_empty_L.
        rewrite lookup_gset_to_gmap.
        destruct (decide (ρ ∈ dom (ls_fuel δ1) ∪ dom fs)) as [Hin|Hin].
        + rewrite option_guard_True //=.

          assert (Hmap: ρ ∈ dom (ls_fuel δ1)).
          { set_solver. }

          destruct (decide (ρ ∈ dom fs)) as [Hinfs|Hinfs].
          * apply elem_of_dom in Hmap as [? Hinfuels]. rewrite Hinfuels /=.
            rewrite Hfuels in Hinfuels; last set_solver. rewrite lookup_fmap in Hinfuels.
            destruct (fs !! ρ); last done. f_equiv. simpl in Hinfuels. injection Hinfuels. intros ?.
            rewrite leibniz_equiv_iff. lia.
          * apply elem_of_dom in Hmap as [? Hinfuels].
            rewrite Hinfuels //.
        + rewrite option_guard_False //=.
          rewrite -> not_elem_of_union in Hin. destruct Hin as [Hin ?].
          rewrite -> not_elem_of_dom in Hin. rewrite Hin //.
      - iPureIntro. split; last first.
        { intros ζ' Hζ'. rewrite lookup_insert_ne; last first.
          { pose proof (locales_of_list_step_incl _ _ _ _ _ Hstep).
            clear Hfueldom Hmappingdom.
            assert (ζ' ∉ locales_of_list tp1); first by set_solver.
            intros contra. simplify_eq.
            destruct Htlen as [tp1' [-> Hlen]].
            inversion Hstep as [? ? e1 ? e2 ? efs t1 t2 Hf1 YY Hprimstep |]. simplify_eq.
            assert (efs = [efork]) as ->.
            { symmetry. assert (length tp1' = length (t1 ++ e2 :: t2)).
              rewrite app_length //=; rewrite app_length //= in Hlen.
              clear Hlen. eapply app_inj_1 =>//. by list_simplifier. }
            rewrite H3 in Hζ'.
            apply Hζ'. apply elem_of_list_fmap.
            eexists (t1 ++ e2 :: t2, _); split =>//.
            - erewrite locale_equiv =>//. apply locales_equiv_middle.
              eapply locale_step_preserve => //.
            - replace (t1 ++ e2 :: t2 ++ [efork]) with ((t1 ++ e2 :: t2) ++ [efork]); last by list_simplifier.
              rewrite prefixes_from_app. set_solver. }

          rewrite lookup_insert_ne; last first.
          { intros <-. rewrite Hsmall in Hmapping; [congruence | set_solver]. }
          apply Hsmall; set_solver.  }

        intros ρ ζ'. rewrite map_lookup_imap.
        destruct (decide (ρ ∈ dom (ls_mapping δ1))) as [Hin|Hin].
        + apply elem_of_dom in Hin as [ζ'' Hρ]. rewrite Hρ. simpl.
          destruct (decide (ρ ∈ R2)) as [Hin'|Hin'].
          * split.
            -- intros. simplify_eq. rewrite lookup_insert. eauto.
            -- intros (ks & Hlk & H'). destruct (decide (ζ' = locale_of tp1 efork)); first congruence.
               rewrite lookup_insert_ne // in Hlk. exfalso.
               assert (ρ ∈ dom fs).
               { set_solver. }
               destruct (decide (ζ = ζ')); simplify_eq.
               ** rewrite lookup_insert in Hlk. set_solver.
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
                 { eapply Hminv. eexists _. split; eauto. set_solver. }
                 congruence. }
               rewrite lookup_insert_ne // in Hin.
               assert (ls_mapping δ1 !! ρ = Some ζ').
               { eapply Hminv. eexists _. split; eauto. }
               congruence.
        + apply not_elem_of_dom in Hin. rewrite Hin /=. split; first done.
          intros (?&Hin'&?). rewrite ls_fuel_dom -ls_mapping_dom in Hdomincl.
          apply not_elem_of_dom in Hin.
          destruct (decide (ζ' = locale_of tp1 efork)).
          { simplify_eq. rewrite lookup_insert in Hin'. simplify_eq. set_solver. }
          rewrite lookup_insert_ne // in Hin'.
          destruct (decide (ζ' = ζ)).
          { simplify_eq. rewrite lookup_insert // in Hin'. simplify_eq. set_solver. }
          rewrite lookup_insert_ne // in Hin'.
          assert (ls_mapping δ1 !! ρ = Some ζ').
          { eapply Hminv. eauto. }
          apply not_elem_of_dom in Hin. congruence. }
    iSplit; first done.
    iSplit; [iSplit|].
    { iPureIntro. destruct (map_choose _ Hnemp) as [ρ[??]]. exists ρ.
      apply Hminv. eexists _. split; eauto. apply elem_of_dom. eauto. }
    iSplit.
    { iPureIntro. intros ρ Hlive Hmd. simpl. inversion Hmd; simplify_eq.
      - rewrite map_lookup_imap.
        assert (Hin: ρ ∈ dom (ls_fuel δ1)).
        { rewrite ls_fuel_dom -ls_mapping_dom elem_of_dom. eauto. }
        apply elem_of_dom in Hin. destruct Hin as [f' Hin'].
        rewrite Hin' /=.
        destruct (decide (ρ ∈ R1 ∪ R2)) as [Hin''|Hin''].
        { rewrite dom_fmap_L -Hunioneq in Hfuels.
          specialize (Hfuels _ Hin''). rewrite lookup_fmap Hin' in Hfuels.
          destruct (fs !! ρ); simplify_eq. simpl in Hfuels. injection Hfuels.
          intros ->. simpl. lia. }
        symmetry in Hsametid. apply Hminv in Hsametid as (?&?&?). set_solver.
      - rewrite map_lookup_imap. simpl in *. clear Hmd.
        destruct (decide (ρ ∈ dom (ls_mapping δ1))) as [Hin|Hin]; last first.
        { apply not_elem_of_dom in Hin. rewrite map_lookup_imap Hin //= in Hissome. by inversion Hissome. }
        apply elem_of_dom in Hin as [ζ' Hin'].
        rewrite map_lookup_imap Hin' /= in Hneqtid.
        destruct (decide (ρ ∈ R2)) as [Hin''|Hin'']; last done.
        rewrite Hfuels; last set_solver. rewrite lookup_fmap.
        assert (Hindom: ρ ∈ dom fs); first by set_solver.
        apply elem_of_dom in Hindom as [f Hindom]. rewrite Hindom /= decide_True /=; [lia|set_solver]. }
    iSplit; last done.
    { iPureIntro. intros ρ' Hρ' _. simpl.
      rewrite map_lookup_imap. rewrite <-ls_fuel_dom, elem_of_dom in Hρ'.
      destruct Hρ' as [f Hf]. rewrite Hf /=. destruct (decide ((ρ' ∈ R1 ∪ R2))); simpl; lia. }
    iPureIntro. intros ρ ζ'. simpl. rewrite map_lookup_imap.
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
      + eapply from_locale_from_equiv =>//; [constructor |]. rewrite H1.
        replace (t1 ++ e1 :: t2 ++ [efork]) with ((t1 ++ e1 :: t2) ++ [efork]);
          last by list_simplifier.
        replace (t1 ++ e2 :: t2 ++ [efork]) with ((t1 ++ e2 :: t2) ++ [efork]);
          last by list_simplifier.
        assert (locales_equiv (t1 ++ e1 :: t2) (t1 ++ e2 :: t2)).
        { apply locales_equiv_middle. eapply locale_step_preserve =>//. }
        apply locales_equiv_from_app =>//. by eapply locales_from_equiv_refl.
    - intros ?; simplify_eq.
      assert (is_Some (from_locale tp1 ζ')) by eauto.
      eapply from_locale_step =>//.
  Qed.

  Definition valid_new_fuelmap (fs1 fs2: gmap (fmrole Mdl) nat) (s1 s2: Mdl) (ρ: fmrole Mdl) :=
    (ρ ∈ live_roles _ s2 -> oleq (fs2 !! ρ) (Some (fuel_limit s2))) ∧
    ρ ∈ dom fs1 ∧
    (forall ρ', ρ' ∈ dom fs2 ∖ live_roles _ s1 -> oleq (fs2 !! ρ') (Some $ fuel_limit s2)) ∧
    (forall ρ', ρ ≠ ρ' -> ρ' ∈ dom fs1 ∩ dom fs2 -> oless (fs2 !! ρ') (fs1 !! ρ')) ∧
    dom fs2 = (dom fs1 ∩ live_roles _ s2) ∪ (live_roles _ s2 ∖ live_roles _ s1).

  Lemma update_step_still_alive
        (extr : execution_trace Λ)
        (auxtr: auxiliary_trace (fair_model Mdl))
        tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ (δ1 : fair_model Mdl) ζ:
    trace_last extr = (tp1, σ1) →
    trace_last auxtr = δ1 ->
    locale_step (tp1, σ1) (Some ζ) (tp2, σ2) ->
    fmtrans _ s1 (Some ρ) s2 -> valid_new_fuelmap fs1 fs2 δ1 s2 ρ ->
    has_fuels ζ fs1 -∗ frag_model_is s1 -∗ model_state_interp tp1 δ1
    ==∗ ∃ (δ2: fair_model Mdl) ℓ,
        ⌜labels_match (Some ζ) ℓ
        ∧ valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[ℓ]: δ2)⌝
        ∗ has_fuels ζ fs2 ∗ frag_model_is s2 ∗ model_state_interp tp2 δ2.
  Proof.
    iIntros (Htrlast Hauxtrlast Hstep Htrans Hfuelsval) "Hfuel Hmod Hsi".

    assert (Hfsne: fs1 ≠ ∅).
    { destruct Hfuelsval as (_&?&_). intros ->. set_solver. }

    iDestruct (has_fuel_in with "Hfuel Hsi") as "%Hxdom"; eauto.
    iDestruct (has_fuel_fuel with "Hfuel Hsi") as %Hfuel; eauto.
    iDestruct (model_state_interp_tids_smaller with "Hsi") as %Hless.

    iDestruct "Hsi" as "(%M&Hafuel&Hamapping&%Hinv&%Hsmall&Hamod)".
    iDestruct (model_agree with "Hamod Hmod") as "%Heq".

    assert (Hfueldom: dom (update_fuel_resource δ1 fs2 s2) = live_roles Mdl s2).
    { unfold update_fuel_resource, fuel_apply. rewrite -leibniz_equiv_iff.
      intros ρ'; split.
      - intros [f Hin]%elem_of_dom. rewrite map_lookup_imap in Hin.
        destruct (decide (ρ' ∈ live_roles _ s2)); first done.
        rewrite lookup_gset_to_gmap option_guard_False // in Hin.
      - intros Hin. destruct (decide (ρ' ∈ dom fs2)) as [[f Hin1]%elem_of_dom|Hin1].
        + apply elem_of_dom. eexists f. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=.
          rewrite decide_True //. apply elem_of_dom. rewrite Hin1; eauto.
        + apply elem_of_dom. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=.
          rewrite decide_False //. apply elem_of_dom. rewrite ls_fuel_dom.
          destruct Hfuelsval as (?&?&?&?&Hdomeq). rewrite Hdomeq in Hin1. set_solver. }

    assert (Hmappingdom: dom (map_imap
                                  (λ ρ' _, if decide (ρ' ∈ live_roles Mdl δ1) then ls_mapping δ1 !! ρ' else Some ζ)
                                  (gset_to_gmap 333 (live_roles Mdl s2))) = live_roles Mdl s2).
    { rewrite -leibniz_equiv_iff. intros ρ'; split.
      - intros [f Hin]%elem_of_dom. rewrite map_lookup_imap in Hin.
        destruct (decide (ρ' ∈ live_roles _ s2)); first done.
        rewrite lookup_gset_to_gmap option_guard_False // in Hin.
      - intros Hin. destruct (decide (ρ' ∈ live_roles _ δ1)) as [Hin1|Hin1].
        + apply elem_of_dom. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=.
          rewrite decide_True //. apply elem_of_dom. rewrite ls_mapping_dom //.
        + apply elem_of_dom. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=.
          rewrite decide_False //. }

    iExists {|
      ls_under := s2;
      ls_fuel := update_fuel_resource δ1 fs2 s2;
      ls_fuel_dom := Hfueldom;
      ls_mapping := map_imap
                      (λ ρ' fold, if decide (ρ' ∈ live_roles _ δ1)
                                  then δ1.(ls_mapping) !! ρ'
                                  else Some ζ)
                      (gset_to_gmap 333 (live_roles _ s2));
      ls_mapping_dom := Hmappingdom;
    |}, (Take_step ρ ζ).
    Unshelve.
    iMod (update_has_fuels _ fs1 fs2 with "Hfuel Hafuel Hamapping") as "(Hafuel & Hfuel & Hmapping)".
    { set_solver. }
    { unfold valid_new_fuelmap in Hfuelsval.
      destruct Hfuelsval as (_&_&?&?&->). rewrite !Heq.
      rewrite ls_fuel_dom. set_solver. }
    iMod (update_model s2 with "Hamod Hmod") as "[Hamod Hmod]".
    iModIntro. iSplit.
    { iSplit; first done. iPureIntro.
      destruct Hfuelsval as (Hlim&Hinfs1m&Hnewlim&Hdec&Hdomeq).
      constructor =>//; split.
      - constructor; simpl; first by rewrite Hauxtrlast Heq //.
        split; first by rewrite Hauxtrlast; apply Hxdom; set_solver.
        split.
        { intros ?? Hmd. inversion Hmd; clear Hmd; simplify_eq.
          + symmetry in Hsametid. rewrite -> Hxdom in Hsametid. simpl.
            unfold update_fuel_resource, fuel_apply.
            rewrite map_lookup_imap lookup_gset_to_gmap.
            destruct (decide (ρ' ∈ live_roles Mdl s2)) as [Hin|Hin].
            * rewrite option_guard_True //=.
              { destruct (decide (ρ' ∈ dom fs2)) as [Hin2|Hin2].
                ** rewrite Hfuel; last set_solver. apply Hdec; [congruence|set_solver].
                ** exfalso. set_solver. }
            * rewrite option_guard_False //=.
              eapply Hin, fm_live_preserved; [done| | congruence].
              rewrite <-Hxdom in Hsametid. rewrite -ls_mapping_dom elem_of_dom. by eauto.
          + simpl in *. unfold update_fuel_resource, fuel_apply.
            rewrite map_lookup_imap lookup_gset_to_gmap.
            destruct (decide (ρ' ∈ live_roles Mdl s2)) as [Hin|Hin].
            * rewrite option_guard_True //=.
              { destruct (decide (ρ' ∈ dom fs2)) as [Hin2|Hin2].
                ** rewrite Hfuel; last set_solver.
                   rewrite Hdomeq in Hin2. exfalso.
                   assert (Hin3: ρ' ∈ dom fs1).
                   { set_solver. }
                   rewrite map_lookup_imap in Hneqtid.
                   rewrite <-Hxdom in Hin3.
                   rewrite Hin3 /= in Hneqtid.
                   rewrite lookup_gset_to_gmap option_guard_True //= in Hneqtid.
                   rewrite decide_True // in Hneqtid.
                ** rewrite map_lookup_imap in Hneqtid.
                   assert (is_Some (ls_mapping (trace_last auxtr) !! ρ')) as [ζ' Hζ'].
                   { apply elem_of_dom. rewrite ls_mapping_dom //. }
                   rewrite lookup_gset_to_gmap option_guard_True //= in Hneqtid.
                   rewrite Hζ' /= decide_True // in Hneqtid. }
            * rewrite option_guard_False //=.
              rewrite map_lookup_imap in Hissome.
              assert (is_Some (ls_mapping (trace_last auxtr) !! ρ')) as [ζ' Hζ'].
              { apply elem_of_dom. rewrite ls_mapping_dom //. }
              rewrite lookup_gset_to_gmap option_guard_False //= in Hissome.
                by inversion Hissome. }
        split.
        + intros ? Hin ?. simplify_eq; simpl.
          unfold update_fuel_resource, fuel_apply.
          rewrite map_lookup_imap lookup_gset_to_gmap.
          destruct (decide (ρ' ∈ live_roles _ s2)) as [Hlive|Hlive].
          * rewrite option_guard_True //=.
            destruct (decide (ρ' ∈ dom fs2)) as [Hin2|Hin2].
            ** rewrite Hfuel; last set_solver. apply oleq_oless, Hdec; [congruence|set_solver].
            ** rewrite <-ls_fuel_dom, elem_of_dom in Hin. destruct Hin as [? ->]. simpl;lia.
          * rewrite option_guard_False //=.
            eapply Hlive, fm_live_preserved =>//. congruence.
        + split.
          { intros Hlive. unfold update_fuel_resource, fuel_apply.
            rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=.
            rewrite decide_True; [by apply Hlim | set_solver]. }
          intros ??. unfold update_fuel_resource, fuel_apply.
          rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=; last set_solver.
          rewrite decide_True; first apply Hnewlim; set_solver.
      - simplify_eq. unfold tids_smaller; simpl.
        intros ρ' ? Hmim.
        rewrite map_lookup_imap in Hmim.
        destruct (decide (ρ' ∈ live_roles _ s2)).
        + rewrite lookup_gset_to_gmap option_guard_True //= in Hmim.
          destruct (ls_mapping (trace_last auxtr) !! ρ') eqn:Heq.
          * simpl in H. destruct (decide (ρ' ∈ live_roles _ (trace_last auxtr))) as [|Hnotin].
            ** rewrite decide_True // in Hmim.
               inversion Hstep; simplify_eq.
               eapply from_locale_step =>//. by eapply Hless.
            ** rewrite <- ls_mapping_dom in Hnotin. apply not_elem_of_dom in Hnotin. congruence.
          * simpl in H. destruct (decide (ρ' ∈ live_roles _ (trace_last auxtr))) as [|Hnotin].
            ** rewrite decide_True // in Hmim.
               inversion Hstep; simplify_eq. eapply from_locale_step =>//.
               by eapply Hless.
            ** rewrite decide_False // in Hmim. simplify_eq.
               inversion Hstep; simplify_eq. eapply from_locale_step =>//.
               eapply Hless. eapply Hxdom. set_solver.
        + rewrite lookup_gset_to_gmap option_guard_False //= in Hmim. }

    iFrame "Hfuel Hmod". iExists _. iFrame.
    iSplitL "Hafuel".
    { simpl. unfold update_fuel_resource.
      destruct Hfuelsval as (?&?&?&?&Hdomeq).
      iApply (own_proper with "Hafuel"). do 3 f_equiv.
      rewrite !ls_fuel_dom !Hdomeq !Heq.
      assert (live_roles _ s1 ∖ dom fs1 = live_roles _ s2 ∖ dom fs2).
      { rewrite Hdomeq -leibniz_equiv_iff.
        eapply set_subseteq_antisymm.
        - intros ρ' [Hin Hnotin]%elem_of_difference.
          apply elem_of_difference. split; last set_solver.
          eapply fm_live_preserved; eauto. set_solver.
        - intros ρ' [Hin Hnotin]%elem_of_difference. apply elem_of_difference.
          split; [set_solver | set_solver]. }
      rewrite -leibniz_equiv_iff.
      eapply set_subseteq_antisymm; first set_solver.
      intros ρ' Hin. apply elem_of_difference; split; [| set_solver].
      apply elem_of_union.
      destruct (decide (ρ' ∈ live_roles _ s1)); set_solver. }
    iPureIntro. split; last first.
    { intros ζ' ?. pose proof (locales_of_list_step_incl _ _ _ _ _ Hstep).
      rewrite lookup_insert_ne; first by apply Hsmall; set_solver.
      intros <-. destruct Hfuelsval as (_&Hfs1&_).
      rewrite <-Hxdom in Hfs1. apply Hinv in Hfs1 as (?&HM&?).
      rewrite Hsmall // in HM. set_solver. }

    intros ρ' ζ'. simpl. rewrite map_lookup_imap.
    destruct (decide (ρ' ∈ live_roles _ s2)) as [Hin|Hnotin].
    - rewrite lookup_gset_to_gmap option_guard_True //=.
      destruct (decide (ρ' ∈ live_roles _ δ1)) as [Hlive|Hlive].
      + destruct (decide (ζ = ζ')) as [<-|Hneq]; last by rewrite lookup_insert_ne //.
        rewrite lookup_insert. split.
        * rewrite Hinv. intros (ks&HM&Hks). eexists. split; first done.
          destruct Hfuelsval as (?&?&?&?&->). apply elem_of_union.
          left. apply elem_of_intersection. split; last done. apply Hxdom.
          apply Hinv. eexists; split; done.
        * intros (ks&HM&Hks). simplify_eq. apply Hxdom.
          destruct Hfuelsval as (?&?&?&?&Hdomeq). rewrite Hdomeq in Hks.
          set_solver.
      + split.
        * intros ?. simplify_eq. rewrite lookup_insert. eexists; split; first done.
          destruct Hfuelsval as (?&?&?&?&->). set_solver.
        * intros (ks&HM&Hks). simplify_eq.
          destruct Hfuelsval as (?&?&?&?&Hdomeq).
          assert (ζ = ζ'); last congruence.
          destruct (decide (ζ = ζ')) as [|Hneq]; first done. exfalso.
          rewrite lookup_insert_ne // in HM. unfold maps_inverse_match in Hinv.
          assert (ls_mapping (trace_last auxtr) !! ρ' = Some ζ').
          { apply Hinv. eexists; done. }
          rewrite -ls_mapping_dom in Hlive. apply not_elem_of_dom in Hlive. set_solver.
    - rewrite lookup_gset_to_gmap option_guard_False //=. split; first done.
      intros (ks & HM & Hks). exfalso.
      destruct (decide (ζ = ζ')) as [Heq'|Heq'].
      + subst ζ'. rewrite lookup_insert in HM. simplify_eq.
        destruct Hfuelsval as (_&_&_&_&Hdomeq). rewrite Hdomeq in Hks.
        set_solver.
      + rewrite lookup_insert_ne // in HM. unfold maps_inverse_match in Hinv.
        assert (ls_mapping δ1 !! ρ' = Some ζ').
        { apply Hinv. eexists _; eauto. }
        eapply Hnotin, fm_live_preserved; eauto.
        * rewrite -Heq -ls_mapping_dom. apply elem_of_dom. eauto.
        * intros <-. destruct Hfuelsval as (?&?&?&?&_). set_solver.
  Qed.

End model_state_lemmas.
