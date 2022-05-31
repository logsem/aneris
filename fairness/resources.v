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
  fairnessGpreS_model_free_roles :> inG Σ (authUR (gset_disjUR (RoleO Mdl)));
}.

Class fairnessGS (Mdl: FairModel) Λ Σ `{Countable (locale Λ)} := FairnessGS {
  fairness_inG :> fairnessGpreS Mdl Λ Σ;
  (** Underlying model *)
  fairness_model_name : gname;
  (** Mapping of threads to sets of roles *)
  fairness_model_mapping_name : gname;
  (** Mapping of roles to fuel *)
  fairness_model_fuel_name : gname;
  (** Set of free/availble roles *)
  fairness_model_free_roles_name : gname;
}.

Global Arguments FairnessGS Mdl Λ  Σ {_ _ _} _ _ _.
Global Arguments fairness_model_name {Mdl Λ Σ _ _} _.
Global Arguments fairness_model_mapping_name {Mdl Λ Σ _ _} _ : assert.
Global Arguments fairness_model_fuel_name {Mdl Λ Σ _ _} _ : assert.
Global Arguments fairness_model_free_roles_name {Mdl Λ Σ _ _} _ : assert.

Definition fairnessΣ (Mdl: FairModel) Λ `{Countable (locale Λ)} : gFunctors := #[
   GFunctor (authUR (optionUR (exclR (ModelO Mdl))));
   GFunctor (authUR (gmapUR (localeO Λ) (exclR (gsetR (RoleO Mdl)))));
   GFunctor (authUR (gmapUR (RoleO Mdl) (exclR natO)));
   GFunctor (authUR (gset_disjUR (RoleO Mdl)))
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

  Definition auth_free_roles_are (FR: gset Role): iProp Σ :=
    own (fairness_model_free_roles_name fG) (● (GSet FR)).

  Definition frag_free_roles_are (FR: gset Role): iProp Σ :=
    own (fairness_model_free_roles_name fG) (◯ (GSet FR)).

  Definition model_state_interp (tp: list $ expr Λ) (δ: LiveState Mdl): iProp Σ :=
    ∃ M FR, auth_fuel_is δ.(ls_fuel) ∗ auth_mapping_is M ∗ auth_free_roles_are FR ∗
      ⌜maps_inverse_match δ.(ls_mapping) M⌝ ∗
      ⌜ ∀ ζ, ζ ∉ locales_of_list tp → M !! ζ = None ⌝ ∗
      auth_model_is δ ∗ ⌜ FR ∩ dom δ.(ls_fuel) = ∅ ⌝.

  Lemma model_state_interp_tids_smaller δ tp :
    model_state_interp tp δ -∗ ⌜ tids_smaller tp δ ⌝.
  Proof.
    iIntros "(%M&%FR&_&_&_&%Hminv&%Hbig&_)". iPureIntro.
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

  Lemma model_free_roles_init `{fairnessGpreS Mdl Λ Σ} (s0: Mdl) (FR: gset _):
    ⊢ |==> ∃ γ,
        own (A := authUR (gset_disjUR (RoleO Mdl))) γ (● GSet FR  ⋅ ◯ GSet FR).
  Proof.
    iMod (own_alloc (● GSet FR  ⋅ ◯ GSet FR)) as (γ) "[H1 H2]".
    { apply auth_both_valid_2 =>//. }
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
    iIntros "Hsi Hs2". iDestruct "Hsi" as (??) "(_&_&_&_&_&Hs1&_)".
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

  Definition update_fuel_resource (δ1: LiveState Mdl) (fs1 fs2: gmap (fmrole Mdl) nat) (s2: Mdl):
    gmap (fmrole Mdl) nat :=
    fuel_apply fs2 (δ1.(ls_fuel (Λ := Λ))) (((dom $ ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2)).

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
    (dom fs' ⊆ dom fs) ->
    has_fuels ζ fs -∗
    auth_fuel_is F -∗
    auth_mapping_is M ==∗
      auth_fuel_is (fuel_apply fs' F LR) ∗
      has_fuels ζ fs' ∗
      auth_mapping_is (<[ ζ := dom fs' ]> M).
  Proof.
    iIntros (LR Hfs Hdom) "Hfuels Hafuels Hamapping".
    rewrite !has_fuels_equiv. iDestruct "Hfuels" as "[Hmapping Hfuels]".
    iMod (update_fuel fs fs' with "Hafuels Hfuels") as "[Hafuels Hfuels]"; [done|set_solver|].
    iMod (update_mapping with "Hamapping Hmapping") as "[Hamapping Hmapping]".
    iModIntro. iFrame.
  Qed.

  Lemma update_has_fuels_no_step_no_change ζ fs fs' F M:
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
    iIntros "[Hζ Hfuels] (%M&%FR&Hafuel&Hamapping &HFR&%Hmapinv&Hamod&Hfr) %ρ".
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
    iIntros "[Hζ Hfuels] (%M&%FR&Hafuel&Hamapping&HFR&%Hmapinv&Hamod)" (ρ Hρ).
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

  Lemma update_no_step_enough_fuel extr (auxtr : auxiliary_trace (fair_model Mdl)) rem c2 fs ζ:
    (dom fs ≠ ∅) ->
    (live_roles _ (trace_last auxtr)) ∩ rem = ∅ →
    rem ⊆ dom fs →
    locale_step (trace_last extr) (Some ζ) c2 ->
    has_fuels_S ζ fs -∗ model_state_interp (trace_last extr).1 (trace_last auxtr)
    ==∗ ∃ δ2 (ℓ : mlabel $ fair_model Mdl),
        ⌜labels_match (Some ζ) ℓ
        ∧ valid_state_evolution_fairness (extr :tr[Some ζ]: c2) (auxtr :tr[ℓ]: δ2)⌝
                                ∗ has_fuels ζ (fs ⇂ (dom fs ∖ rem)) ∗ model_state_interp c2.1 δ2.
  Proof.
    iIntros "%HnotO %Holdroles %Hincl %Hstep Hf Hmod".
    destruct c2 as [tp2 σ2].
    destruct (set_choose_L _ HnotO) as [??].
    iDestruct (has_fuel_in with "Hf Hmod") as %Hxdom; eauto.
    iDestruct (has_fuel_fuel with "Hf Hmod") as "%Hfuel"; eauto.
    iDestruct (model_state_interp_tids_smaller with "Hmod") as %Hζs.
    iDestruct "Hmod" as "(%M & %FR & Hfuel & Hamapping & HFR & %Hminv & %Hlocssmall & Hmodel & %HFR)".
    unfold has_fuels_S.
    simpl in *.

    set new_dom := ((dom (ls_fuel (trace_last auxtr)) ∪ dom fs) ∖ rem).
    set new_mapping := ls_mapping (trace_last auxtr) ⇂ new_dom.

    assert (dom (fuel_apply (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs) (ls_fuel (trace_last auxtr))
                   ((dom (ls_fuel (trace_last auxtr)) ∪ dom fs) ∖ rem)) = new_dom) as Hnewdom.
    { rewrite /fuel_apply map_imap_dom_eq ?dom_gset_to_gmap //.
      intros ρ0 _ Hindom.
      destruct (decide (ρ0 ∈ dom (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs))) as [Hinf|Hninf];
        first by apply elem_of_dom.
      apply elem_of_difference in Hindom as [Hin1 ?].
      apply elem_of_union in Hin1 as [?|Hin2]; first by apply elem_of_dom.
      exfalso. apply Hninf. apply elem_of_dom in Hin2 as [f ?].
      eapply elem_of_dom_2. rewrite map_filter_lookup_Some. split =>//.
      apply elem_of_difference; split =>//. by eapply elem_of_dom_2. }

    assert (Hsamedoms: dom new_mapping =
                       dom (fuel_apply (fs ⇂ (dom fs ∖ rem))
                                       (ls_fuel (trace_last auxtr))
                                       ((dom (ls_fuel (trace_last auxtr)) ∪ dom fs) ∖ rem))).
    { rewrite /new_mapping /new_dom. unfold fuel_apply.
      assert (dom fs ⊆ dom (trace_last auxtr).(ls_fuel)).
      { intros ρ Hin. rewrite elem_of_dom Hfuel; last set_solver.
        apply elem_of_dom in Hin as [? Hin]. rewrite lookup_fmap Hin //=. }
      rewrite map_imap_dom_eq; last first.
      { intros ρ _ Hin. rewrite dom_gset_to_gmap in Hin.
        destruct (decide (ρ ∈ dom $ fs ⇂ (dom fs ∖ rem))) as [Hin'|_].
        * by apply elem_of_dom.
        * apply elem_of_dom. set_solver. }
      rewrite dom_domain_restrict ?dom_gset_to_gmap ?ls_same_doms //. set_solver. }
    assert (Hfueldom: live_roles _ (trace_last auxtr) ⊆
     dom (fuel_apply (fs ⇂ (dom fs ∖ rem))
                     (ls_fuel (trace_last auxtr))
                     ((dom (ls_fuel (trace_last auxtr)) ∪ dom fs) ∖ rem))).
    { rewrite /fuel_apply Hnewdom.
      intros ρ Hin. apply elem_of_difference; split;
        [apply ls_fuel_dom in Hin; set_solver | set_solver]. }

    iMod (update_has_fuels_no_step ζ (S <$> fs) (fs ⇂ (dom fs ∖ rem)) with "[Hf] [Hfuel] [Hamapping]") as "(Hafuels&Hfuels&Hamapping)" =>//.
    { rewrite -dom_empty_iff_L. set_solver. }
    { rewrite dom_domain_restrict; set_solver. }

    iModIntro.
    iExists {|
      ls_under := (trace_last auxtr).(ls_under);
      ls_fuel := _;
      ls_fuel_dom := Hfueldom;
      ls_same_doms := Hsamedoms;
    |}.
    iExists (Silent_step ζ). simpl.
    iSplit; last first.
    { rewrite (dom_fmap_L _ fs). iFrame "Hfuels". iExists _, FR. rewrite /maps_inverse_match //=. iFrame.
      assert (dom fs ⊆ dom (ls_fuel $ trace_last auxtr)).
      { intros ρ Hin. setoid_rewrite dom_fmap in Hxdom.
        specialize (Hxdom ρ). rewrite -ls_same_doms. apply elem_of_dom. exists ζ.
        by apply Hxdom. }
      iSplit.
      { iApply (auth_fuel_is_proper with "Hafuels"). f_equiv.
        rewrite dom_domain_restrict; last set_solver.
        replace (dom fs ∖ (dom fs ∖ rem)) with rem; [set_solver|].
        rewrite -leibniz_equiv_iff. intros ρ. split; [set_solver|].
        intros [? [?|?]%not_elem_of_difference]%elem_of_difference =>//. }
      iPureIntro. split; last split.
      - intros ρ ζ'. rewrite /new_mapping dom_domain_restrict; last set_solver. split.
        + intros [Hlk Hin]%map_filter_lookup_Some. destruct (decide (ζ' = ζ)) as [->|Hneq].
          * rewrite lookup_insert. eexists; split=>//. set_solver.
          * rewrite lookup_insert_ne //. by apply Hminv.
        + intros Hin. destruct (decide (ζ' = ζ)) as [->|Hneq].
          * rewrite lookup_insert in Hin. apply map_filter_lookup_Some.
            destruct Hin as (?&?&?). simplify_eq. split; last set_solver.
            apply Hxdom. rewrite dom_fmap. set_solver.
          * rewrite lookup_insert_ne // -Hminv in Hin. apply map_filter_lookup_Some; split=>//.
            rewrite /new_dom. apply elem_of_difference; split.
            ** apply elem_of_dom_2 in Hin. rewrite ls_same_doms in Hin. set_solver.
            ** assert (ρ ∉ dom fs); last set_solver. rewrite dom_fmap_L in Hxdom.
               intros contra%Hxdom. congruence.
      - intros ζ0 Hnotin. apply lookup_insert_None; split.
        + apply Hlocssmall.
          destruct (trace_last extr).
          have ? := locales_of_list_step_incl _ _ _ _ _ Hstep. simpl.
          clear Hfueldom Hsamedoms. set_solver.
        + intros <-.
          destruct (trace_last extr).
          have ? := locales_of_list_step_incl _ _ _ _ _ Hstep. simpl.
          clear Hfueldom Hsamedoms. inversion Hstep. simplify_eq.
          assert (locale_of t1 e1 ∈ locales_of_list (t1 ++ e1 :: t2)); last set_solver.
          apply locales_of_list_from_locale_from.
          rewrite from_locale_from_Some // prefixes_from_spec. eexists _,_. by list_simplifier.
      - rewrite Hnewdom /new_dom. apply elem_of_equiv_empty_L. intros ρ [Hin1 Hin2]%elem_of_intersection.
        assert (ρ ∈ dom (ls_fuel (trace_last auxtr))) by set_solver. set_solver. }
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
        { rewrite map_filter_lookup Heqf /= option_guard_True //. set_solver. }
        rewrite decide_True // ?Heqfilter ?lookup_fmap ?Heqf /=; last by eapply elem_of_dom_2. lia.
      + rewrite /= /new_mapping map_filter_lookup in Hneqtid.
        pose proof Hin as Hin2. rewrite -ls_same_doms in Hin2. apply elem_of_dom in Hin2 as [f Hf].
        rewrite Hf /= option_guard_True // in Hneqtid.
    - intros ρ' Hin _. simpl. destruct (decide (ρ' ∈ rem)) as [Hin'|Hnin'].
      + right; split; last set_solver. rewrite /fuel_apply map_imap_dom_eq ?dom_gset_to_gmap; first set_solver.
        intros ρ0 _ Hin0. destruct (decide (ρ0 ∈ dom (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs))) as [?|Hnin];
          first by apply elem_of_dom.
        apply elem_of_difference in Hin0 as [Hin1 ?].
        apply elem_of_union in Hin1 as [?|Hin2]; first by apply elem_of_dom.
        exfalso. apply Hnin. apply elem_of_dom in Hin2 as [f ?].
        eapply elem_of_dom_2. rewrite map_filter_lookup_Some. split =>//.
        apply elem_of_difference; split =>//. by eapply elem_of_dom_2.
      + left. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=; last set_solver.
        apply elem_of_dom in Hin as [f Hf].
        destruct (decide (ρ' ∈ dom (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs))) as [Hin|?];
          last by rewrite !Hf //=.
        apply elem_of_dom in Hin as [f' Hf']. rewrite Hf'.
        apply map_filter_lookup_Some in Hf' as [Hfs Hf'].
        rewrite Hfuel ?lookup_fmap ?Hfs /=; [lia |]. rewrite dom_fmap; set_solver.
    - rewrite Hnewdom. assert (dom fs ⊆ dom $ ls_fuel (trace_last auxtr)); last set_solver.
        intros ρ Hin. apply elem_of_dom. rewrite Hfuel ?dom_fmap // -elem_of_dom dom_fmap //.
    - unfold tids_smaller; simpl. intros ρ ζ0 Hin.
      destruct (trace_last extr); destruct (trace_last extr).
      eapply from_locale_step =>//.
      rewrite /tids_smaller /= in Hζs. eapply Hζs.
      rewrite /new_mapping map_filter_lookup_Some in Hin.
      by destruct Hin.
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
    iDestruct "Hmod" as (M FR) "(Haf&Ham&HFR&%Hminv&%Hsmall&Hamod&%HFR)".

    pose Hlocincl := locales_of_list_step_incl _ _ _ _ _ Hstep.

    iMod (update_has_fuels_no_step_no_change ζ (S <$> fs) fs with "Hf Haf Ham") as "(Haf&Hf&Ham)".
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

    iMod (update_mapping_new_locale ζ (locale_of tp1 efork) _ R1 R2 with "Ham Hf") as "(Ham&HR1&HR2)"; eauto.

    pose δ1 := trace_last auxtr.
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
    { unfold has_fuels. rewrite dom_domain_restrict; [|set_solver]. iFrame.
      iApply (big_sepS_impl with "Hf2"). iIntros "!#" (x Hin) "(%f&%&?)".
      iExists _; iFrame. iPureIntro. rewrite map_filter_lookup_Some //. }
    iSplitL "Hf1 HR1".
    { unfold has_fuels. rewrite dom_domain_restrict; [|set_solver]. iFrame.
      iApply (big_sepS_impl with "Hf1"). iIntros "!#" (x Hin) "(%f&%&?)".
      iExists _; iFrame. iPureIntro. rewrite map_filter_lookup_Some //. }
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
      - iPureIntro. split; first last; [split|].
        { intros ζ' Hζ'. rewrite lookup_insert_ne; last first.
          { pose proof (locales_of_list_step_incl _ _ _ _ _ Hstep).
            clear Hfueldom Hsamedoms.
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
          intros (?&Hin'&?). rewrite -ls_same_doms in Hdomincl.
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
    iSplit.
    { iPureIntro. intros ρ' Hρ' _. simpl. left.
      rewrite map_lookup_imap. rewrite elem_of_dom in Hρ'.
      destruct Hρ' as [f Hf]. rewrite Hf /=. destruct (decide ((ρ' ∈ R1 ∪ R2))); simpl; lia. }
    iSplit; [simpl| done]. rewrite map_imap_dom_eq //.
    by intros ρ??; destruct (decide (ρ ∈ R1 ∪ R2)).
  Qed.

  Definition valid_new_fuelmap (fs1 fs2: gmap (fmrole Mdl) nat) (s1 s2: Mdl) (ρ: fmrole Mdl) :=
    (ρ ∈ live_roles _ s2 -> oleq (fs2 !! ρ) (Some (fuel_limit s2))) ∧
    (ρ ∉ live_roles _ s2 -> ρ ∈ dom fs1 ∩ dom fs2 -> oless (fs2 !! ρ) (fs1 !! ρ)) ∧
    ρ ∈ dom fs1 ∧
    (forall ρ', ρ' ∈ dom fs2 ∖ dom fs1 -> oleq (fs2 !! ρ') (Some $ fuel_limit s2)) ∧
    (forall ρ', ρ ≠ ρ' -> ρ' ∈ dom fs1 ∩ dom fs2 -> oless (fs2 !! ρ') (fs1 !! ρ')) ∧
    (dom fs1 ∖ {[ ρ ]}) ∪ (live_roles _ s2 ∖ live_roles _ s1) ⊆ dom fs2 ∧
    dom fs2 ⊆
      (* new roles *) (live_roles _ s2 ∖ live_roles _ s1) ∪
      (* surviving roles *) (live_roles _ s2 ∩ live_roles _ s1 ∩ dom fs1) ∪
      (* already dead *) (dom fs1 ∖ live_roles _ s1) ∪
      (* new deads *) ((live_roles _ s1 ∖ live_roles _ s2) ∩ dom fs1).

  Ltac by_contradiction :=
    match goal with
    | |- ?goal => destruct_decide (decide (goal)); first done; exfalso
    end.

  Lemma update_step_still_alive
        (extr : execution_trace Λ)
        (auxtr: auxiliary_trace (fair_model Mdl))
        tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ (δ1 : fair_model Mdl) ζ fr1:
    (live_roles _ s2 ∖ live_roles _ s1) ⊆ fr1 ->
    trace_last extr = (tp1, σ1) →
    trace_last auxtr = δ1 ->
    locale_step (tp1, σ1) (Some ζ) (tp2, σ2) ->
    fmtrans _ s1 (Some ρ) s2 -> valid_new_fuelmap fs1 fs2 δ1 s2 ρ ->
    has_fuels ζ fs1 -∗ frag_model_is s1 -∗ model_state_interp tp1 δ1 -∗
    frag_free_roles_are fr1
    ==∗ ∃ (δ2: fair_model Mdl) ℓ,
        ⌜labels_match (Some ζ) ℓ
        ∧ valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[ℓ]: δ2)⌝
        ∗ has_fuels ζ fs2 ∗ frag_model_is s2 ∗ model_state_interp tp2 δ2 ∗
        frag_free_roles_are (fr1 ∖ (live_roles _ s2 ∖ live_roles _ s1)).
  Proof.
    iIntros (Hfr_new Htrlast Hauxtrlast Hstep Htrans Hfuelsval) "Hfuel Hmod Hsi Hfr1".

    assert (Hfsne: fs1 ≠ ∅).
    { destruct Hfuelsval as (_&_&?&_). intros ->. set_solver. }

    iDestruct (has_fuel_in with "Hfuel Hsi") as "%Hxdom"; eauto.
    iDestruct (has_fuel_fuel with "Hfuel Hsi") as %Hfuel; eauto.
    iDestruct (model_state_interp_tids_smaller with "Hsi") as %Hless.

    iDestruct "Hsi" as "(%M&%FR&Hafuel&Hamapping&HFR&%Hinv&%Hsmall&Hamod&%HFR)".
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
      { epose proof ls_fuel_dom. intros ρ' Hin.
        destruct Hfuelsval as (?&?&?&?&?&?).
        destruct (decide (ρ' ∈ live_roles _ δ1)).
        - apply elem_of_difference; split; [set_solver|].
          intros [? Habs]%elem_of_difference.
          destruct (decide (ρ' = ρ)).
          + simplify_eq. apply not_elem_of_dom in Habs.
            rewrite -> Habs in *. simpl in *. eauto.
          + apply Habs. assert (ρ' ∈ dom fs1 ∖ {[ρ]}); set_solver.
        - apply elem_of_difference; split; [apply elem_of_union; right; set_solver|set_solver]. }
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

      assert (ρ0 ∈ live_roles _ s2 ∖ live_roles _ s1) by set_solver.
      assert (ρ0 ∈ fr1) by set_solver.
      assert (ρ0 ∈ FR) by set_solver.
      assert (ρ0 ∉ dom (ls_fuel δ1)) by set_solver.
      done. }
    iMod (update_model s2 with "Hamod Hmod") as "[Hamod Hmod]".
    iMod (update_free_roles (live_roles Mdl s2 ∖ live_roles Mdl s1)
           with "HFR Hfr1") as "[HFR Hfr2]"; [set_solver|].
    iModIntro. iSplit.
    { iSplit; first done. iPureIntro.
      destruct Hfuelsval as (Hlim&Hzombie&Hinfs1m&Hnewlim&Hdec&Hinf&Hsup).
      constructor =>//; split.
      - constructor; simpl; first by rewrite Hauxtrlast Heq //.
        split; first by rewrite Hauxtrlast; apply Hxdom; set_solver.
        split.
        { intros ??? Hmd. inversion Hmd; clear Hmd; simplify_eq.
          + symmetry in Hsametid. rewrite -> Hxdom in Hsametid. simpl.
            unfold update_fuel_resource, fuel_apply.
            rewrite map_lookup_imap lookup_gset_to_gmap.
            destruct (decide (ρ' ∈ live_roles Mdl s2 ∪ dom fs2)) as [Hin|Hin].
            * rewrite option_guard_True //=.
              { destruct (decide (ρ' ∈ dom fs2)) as [Hin2|Hin2].
                ** rewrite Hfuel; last set_solver. apply Hdec; [congruence|set_solver].
                ** exfalso. set_solver. }
              apply elem_of_difference; split; [set_solver|].
              apply not_elem_of_difference; right.
              apply elem_of_union in Hin as [|]; [|done].
              destruct (decide (ρ' = ρ)); simplify_eq.
              apply Hinf; set_solver.
            * rewrite option_guard_False //=.
              ** assert (ρ' ∈ dom fs2); set_solver.
              ** apply not_elem_of_difference; right; set_solver.
          + simpl in *. unfold update_fuel_resource, fuel_apply.
            rewrite map_lookup_imap lookup_gset_to_gmap.

            destruct (decide (ρ' ∈ (dom (ls_fuel (trace_last auxtr)) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hin|Hin].
            * rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //= decide_True //= in Hneqtid.
            * apply not_elem_of_difference in Hin as [?|Hin]; [set_solver|].
              apply elem_of_difference in Hin as [??].
              rewrite map_lookup_imap lookup_gset_to_gmap /= option_guard_False /= in Hissome;
                [inversion Hissome; congruence|set_solver].
          + simpl in *. rewrite Hfuel; last set_solver. unfold update_fuel_resource, fuel_apply.
            rewrite Hnewdom in Hnotdead. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=.
            assert (ρ' ∈ dom fs2) by set_solver.
            rewrite decide_True; [apply Hzombie =>//; set_solver | done]. }
        split.
        + intros ? Hin ?. simplify_eq; simpl.
          unfold update_fuel_resource, fuel_apply.
          rewrite map_lookup_imap lookup_gset_to_gmap.
          destruct (decide (ρ' ∈ (dom (ls_fuel (trace_last auxtr)) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hlive|Hlive].
          * rewrite option_guard_True //=.
            apply elem_of_difference in Hlive as [Hin1 Hnin].
            apply not_elem_of_difference in Hnin.

            destruct (decide (ρ' ∈ dom fs2)) as [Hin2|Hin2].
            ** destruct (decide (ρ' ∈ live_roles _ (trace_last auxtr)));left.
               *** destruct (decide (ρ' ∈ dom fs1)).
                   { rewrite Hfuel //. apply oleq_oless, Hdec; [congruence|set_solver]. }
                   { exfalso. set_solver. }
               *** assert (ρ' ∉ live_roles _ s2).
                   { by_contradiction. assert (ρ' ∈ fr1); [eapply elem_of_subseteq; eauto; set_solver|].
                     assert (ρ' ∈ FR); [eapply elem_of_subseteq; eauto; set_solver|set_solver]. }
                   assert (ρ' ∈ dom fs1). set_solver.
                   rewrite Hfuel //. apply oleq_oless, Hdec; [congruence|set_solver].
            ** left. rewrite elem_of_dom in Hin. destruct Hin as [? ->]. simpl;lia.
          * right; split.
            ** eapply not_elem_of_weaken; [|by apply map_imap_dom_inclusion; rewrite dom_gset_to_gmap].
               rewrite dom_gset_to_gmap //.
            ** apply not_elem_of_difference in Hlive as [?|Hlive]; [set_solver|].
               apply elem_of_difference in Hlive as [? Habs].
               exfalso. apply Habs. set_solver.
        + split.
          { intros Hlive. unfold update_fuel_resource, fuel_apply.
          destruct (decide (ρ ∈ (dom (ls_fuel (trace_last auxtr)) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hin|Hnin].
          - rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=; last set_solver.
            rewrite decide_True; [by apply Hlim |set_solver].
          - exfalso; apply not_elem_of_difference in Hnin as [Hnin|Hnin].
            + assert (ρ ∉ live_roles _ (trace_last auxtr)).
              eapply not_elem_of_weaken => //.
              { epose proof ls_fuel_dom. set_solver. }
              assert (ρ ∈ dom fs2) by set_solver. set_solver.
            + apply elem_of_difference in Hnin as [? Hnin].
              apply not_elem_of_dom in Hnin. rewrite Hnin /= in Hlim.
              by apply Hlim. }
          split.
          { intros ρ'. unfold update_fuel_resource, fuel_apply => Hin.
            rewrite map_imap_dom_eq in Hin; last first.
            { intros ρ0 _ Hin'. destruct (decide (ρ0 ∈ dom fs2)); [by apply elem_of_dom|].
              rewrite dom_gset_to_gmap elem_of_difference in Hin'.
              destruct Hin' as [Hin' ?]. apply elem_of_union in Hin' as [?|?]; [by apply elem_of_dom|done]. }
            rewrite dom_gset_to_gmap in Hin. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True /=; last set_solver.
            assert (ρ' ∈ dom fs2) by set_solver. rewrite decide_True //. apply Hnewlim. apply elem_of_difference; split =>//.
            intros contra%Hxdom%elem_of_dom_2. rewrite ls_same_doms in contra. simplify_eq. set_solver. }
          intros ρ0 Hin.
          assert (ρ0 ∉ live_roles _ (trace_last auxtr)).
          { eapply not_elem_of_weaken; last apply ls_fuel_dom. set_solver. }
          apply elem_of_difference in Hin as [Hin1 Hnin].
          assert (ρ0 ∈ live_roles _ s2).
          { by_contradiction.
            assert (ρ0 ∈ dom fs2).
            { unfold update_fuel_resource, fuel_apply in Hin1.
              eapply elem_of_subseteq in Hin1; last apply map_imap_dom_inclusion.
              rewrite dom_gset_to_gmap in Hin1. set_solver. }
            exfalso. assert (Hinabs: ρ0 ∈ dom fs1) by set_solver.
            apply not_elem_of_dom in Hnin. rewrite Hauxtrlast Hfuel // in Hnin.
            apply elem_of_dom in Hinabs. rewrite Hnin in Hinabs. simpl in Hinabs.
            by inversion Hinabs. }
          set_solver.
      - simplify_eq. unfold tids_smaller; simpl.
        intros ρ' ? Hmim.
        rewrite map_lookup_imap in Hmim. rewrite lookup_gset_to_gmap in Hmim.
        destruct (decide (ρ' ∈ (dom (ls_fuel (trace_last auxtr)) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2)));
          last by rewrite option_guard_False in Hmim.
        rewrite option_guard_True //= in Hmim.
        destruct (decide (ρ' ∈ dom (ls_fuel (trace_last auxtr)))).
        + rewrite decide_True // in Hmim.
          inversion Hstep; simplify_eq.
          eapply from_locale_step =>//. by eapply Hless.
        + rewrite decide_False // in Hmim. simplify_eq.
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
              set_solver. }
            { intros (?&?&?). simplify_eq. apply Hxdom.
              destruct Hfuelsval as (?&?&?&?&?). by_contradiction.
              assert (ρ' ∈ live_roles Mdl s2 ∖ live_roles Mdl (trace_last auxtr)) by set_solver.
              assert (ρ' ∈ fr1) by set_solver.
              assert (ρ' ∈ FR) by set_solver.
              assert (ρ' ∉ dom $ ls_fuel (trace_last auxtr)) by set_solver.
              done. }
          * rewrite lookup_insert_ne //.
        + split.
          * intros Htid. simplify_eq. rewrite lookup_insert. eexists; split=>//.
            set_solver.
          * assert (ρ' ∈ dom fs2) by set_solver. intros Hm. by_contradiction.
            rewrite lookup_insert_ne in Hm; last congruence.
            rewrite -Hinv in Hm. apply elem_of_dom_2 in Hm. rewrite ls_same_doms // in Hm.
      - destruct Hfuelsval as (?&?&?&?&Hinf&?). rewrite option_guard_False //=. split; first done.
        destruct (decide (ζ' = ζ)) as [->|Hneq].
        { rewrite lookup_insert //. intros (?&?&?). simplify_eq. set_solver. }
        rewrite lookup_insert_ne //.
        rewrite -Hinv. intros Habs.

        apply not_elem_of_difference in Hnotin as [Hnin|Hin].
        + apply elem_of_dom_2 in Habs. rewrite ls_same_doms in Habs. set_solver.
        + apply elem_of_difference in Hin as [Hin Hnin].
          apply Hxdom in Hin. congruence. }
    split.
    { intros ζ' ?. pose proof (locales_of_list_step_incl _ _ _ _ _ Hstep). simpl.
      rewrite lookup_insert_ne; first by apply Hsmall; set_solver.
      intros <-. destruct Hfuelsval as (_&_&Hfs1&_).
      rewrite <-Hxdom in Hfs1. apply Hinv in Hfs1 as (?&HM&?).
      rewrite Hsmall // in HM. set_solver. }
    { simpl. rewrite /update_fuel_resource /fuel_apply.
      rewrite map_imap_dom_eq ?dom_gset_to_gmap.
      + apply elem_of_equiv_empty_L. intros ρ' [Hin1 Hin2]%elem_of_intersection.
        apply elem_of_difference in Hin1 as [Hin11 Hin12].
        apply not_elem_of_difference in Hin12.
        apply elem_of_difference in Hin2 as [Hin21 Hin22].
        apply not_elem_of_difference in Hin22.
        assert (ρ' ∉ dom $ ls_fuel δ1) by set_solver.
        assert (ρ' ∈ dom fs2) by set_solver.
        destruct Hin12 as [Hin12|Hin12]; last by (epose proof ls_fuel_dom; set_solver).
        destruct Hfuelsval as (?&?&?&?&?&?).
        assert (ρ' ∉ dom fs1); last set_solver.
        intros contra. pose proof (Hfuel _ contra) as Habs. apply elem_of_dom in contra as [? contra].
        rewrite contra in Habs. apply elem_of_dom_2 in Habs. done.
    + intros ρ' _ Hin. destruct (decide (ρ' ∈ dom fs2)) as [Hin'|].
      * apply elem_of_dom in Hin' as [? ->]. done.
      * assert (ρ' ∈ dom (ls_fuel δ1)) as Hin' by set_solver. apply elem_of_dom in Hin' as [? ->]. done. }
Qed.

End model_state_lemmas.
