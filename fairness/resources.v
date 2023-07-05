From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel.

Canonical Structure ModelO (Mdl : FairModel) := leibnizO Mdl.
Canonical Structure RoleO (Mdl : FairModel) := leibnizO (Mdl.(fmrole)).
Canonical Structure localeO (Λ : language) := leibnizO (locale Λ).

(* TODO: why require LiveModel here? *)
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

  Definition model_state_interp (tp: list $ expr Λ) (δ: LiveState Λ M): iProp Σ :=
    ∃ M FR, auth_fuel_is δ.(ls_fuel) ∗ auth_mapping_is M ∗ auth_free_roles_are FR ∗
      ⌜maps_inverse_match δ.(ls_mapping) M⌝ ∗
      ⌜ ∀ ζ, ζ ∉ locales_of_list tp → M !! ζ = None ⌝ ∗
      auth_model_is δ ∗ ⌜ FR ∩ dom δ.(ls_fuel) = ∅ ⌝.

  Lemma model_state_interp_tids_smaller δ tp :
    model_state_interp tp δ -∗ ⌜ tids_smaller tp δ ⌝.
  Proof.
    iIntros "(%m&%FR&_&_&_&%Hminv&%Hbig&_)". iPureIntro.
    intros ρ ζ Hin.
    assert (¬ (ζ ∉ locales_of_list tp)).
    - intros contra.
      apply Hminv in Hin as [? [Hsome _]].
      specialize (Hbig _ contra).
      by rewrite Hbig in Hsome.
    - destruct (decide (ζ ∈ locales_of_list tp)) as [Hin'|] =>//.
      apply elem_of_list_fmap in Hin' as [[tp' e'] [-> Hin']].
      unfold from_locale. exists e'. by apply from_locale_from_Some.
  Qed.
  
  Global Instance frag_free_roles_are_proper: Proper (equiv ==> equiv) frag_free_roles_are.
  Proof. intros ???. set_solver. Qed.    

  Global Instance frag_mapping_is_proper: Proper (equiv ==> equiv) frag_mapping_is.
  Proof. intros ???. set_solver. Qed. 


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


Section AuxDefs.
  Context `{LM: LiveModel Λ M}.

  Definition valid_new_fuelmap (fs1 fs2: gmap (fmrole M) nat) (s1 s2: M) (ρ: fmrole M) :=
    (ρ ∈ live_roles _ s2 -> oleq (fs2 !! ρ) (Some (LM.(lm_fl) s2))) ∧
    (ρ ∉ live_roles _ s2 -> ρ ∈ dom fs1 ∩ dom fs2 -> oless (fs2 !! ρ) (fs1 !! ρ)) ∧
    ρ ∈ dom fs1 ∧
    (forall ρ', ρ' ∈ dom fs2 ∖ dom fs1 -> oleq (fs2 !! ρ') (Some $ LM.(lm_fl) s2)) ∧
    (forall ρ', ρ ≠ ρ' -> ρ' ∈ dom fs1 ∩ dom fs2 -> oless (fs2 !! ρ') (fs1 !! ρ')) ∧
    (dom fs1 ∖ {[ ρ ]}) ∪ (live_roles _ s2 ∖ live_roles _ s1) ⊆ dom fs2 ∧
    dom fs2 ⊆
      (* new roles *) (live_roles _ s2 ∖ live_roles _ s1) ∪
      (* surviving roles *) (live_roles _ s2 ∩ live_roles _ s1 ∩ dom fs1) ∪
      (* already dead *) (dom fs1 ∖ live_roles _ s1) ∪
      (* new deads *) ((live_roles _ s1 ∖ live_roles _ s2) ∩ dom fs1).

End AuxDefs.

Section PartialOwnership.

  Context `{LM: LiveModel Λ M}.
  Context `{Countable (locale Λ)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.
  (* Context `{invGS Σ}.  *)
  Context `{invGS_gen HasNoLc Σ}. 
  Context `{iLM: LiveModel Λ iM}. (* fuel construction over inner model *)


  (* TODO: rename *)
  Class PartialModelPredicatesPre := {
      partial_model_is: fmstate iM -> iProp Σ;
      partial_free_roles_are: gset (fmrole iM) → iProp Σ;
      partial_fuel_is: gmap (fmrole iM) nat → iProp Σ;
      partial_mapping_is: gmap (locale Λ) (gset (fmrole iM)) → iProp Σ;
      
      partial_model_is_Timeless :> forall s, Timeless (partial_model_is s);
      partial_fuel_is_Timeless :> forall fs, Timeless (partial_fuel_is fs);
      partial_mapping_is_Timeless :> forall rs, Timeless (partial_mapping_is rs);
      partial_free_roles_are_Timeless :> forall s, Timeless (partial_free_roles_are s);

      partial_free_roles_are_Proper :> Proper (equiv ==> equiv) partial_free_roles_are;
      partial_mapping_is_Proper :> Proper (equiv ==> equiv) partial_mapping_is;

      (* partial_fuels_is_sep: forall fs, partial_fuel_is fs ⊣⊢ [∗ map] ρ↦f ∈ fs, partial_fuel_is {[ ρ := f ]}; *)
      partial_fuels_is_sep: forall fs1 fs2 (DISJ: fs1 ##ₘ fs2),
        partial_fuel_is (fs1 ∪ fs2) ⊣⊢ partial_fuel_is fs1 ∗ partial_fuel_is fs2;
      partial_free_roles_are_sep: forall fr1 fr2 (DISJ: fr1 ## fr2), 
        partial_free_roles_are (fr1 ∪ fr2) ⊣⊢ partial_free_roles_are fr1 ∗ partial_free_roles_are fr2;
      partial_free_roles_empty: ⊢ |==> partial_free_roles_are ∅;      
  }.

  Notation "tid ↦M R" := (partial_mapping_is {[ tid := R ]}) (at level 33).
  Notation "tid ↦m ρ" := (partial_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
  Notation "ρ ↦F f" := (partial_fuel_is {[ ρ := f ]}) (at level 33).

  Section PartialModelPredicates.
    Context {PMPP: PartialModelPredicatesPre}. 

    Notation Role := (iM.(fmrole)).

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

    Definition fuels_ge (fs: gmap Role nat) b :=
      forall ρ f (FUEL: fs !! ρ = Some f), f >= b. 
    
    Lemma has_fuels_ge_S_exact b tid (fs: gmap Role nat)
      (FUELS_GE: fuels_ge fs (S b)):
      has_fuels tid fs -∗
      has_fuels_S tid (fmap (fun f => f - 1) fs). 
    Proof.
      iIntros "FUELS".
      rewrite /has_fuels_S /has_fuels.
      do 2 rewrite dom_fmap_L. 
      iDestruct "FUELS" as "(T & FUELS)". iFrame.
      
      iApply (big_sepS_impl with "[$]").
      
      iModIntro. iIntros (ρ) "%DOMρ [%f [%TT Fρ]]".
      iExists _. iFrame. iPureIntro.
      apply lookup_fmap_Some. exists (f - 1). split.
      { red in FUELS_GE. specialize (FUELS_GE _ _ TT). lia. }
      apply lookup_fmap_Some. eauto.
    Qed.

    Lemma fuels_ge_minus1 fs b (FUELS_GE: fuels_ge fs (S b)):
      fuels_ge ((λ f, f - 1) <$> fs) b.
    Proof. 
      red. intros.
      pose proof (elem_of_dom_2 _ _ _ FUEL) as DOM.
      rewrite dom_fmap_L in DOM.
      simpl in FUEL.
      apply lookup_fmap_Some in FUEL as (f' & <- & FUEL).
      red in FUELS_GE. specialize (FUELS_GE _ _ FUEL). lia.
    Qed. 
    
    Lemma has_fuels_ge_S b tid (fs: gmap Role nat)
      (FUELS_GE: fuels_ge fs (S b)):
      has_fuels tid fs -∗
      ∃ fs', has_fuels_S tid fs' ∗ ⌜fuels_ge fs' b⌝.
    Proof.
      iIntros "FUELS".
      iDestruct (has_fuels_ge_S_exact with "FUELS") as "FUELS"; eauto.
      iExists _. iFrame. 
      iPureIntro. by apply fuels_ge_minus1. 
    Qed.

    Let update_no_step_enough_fuel_def (extr : finite_trace (cfg Λ) (olocale Λ)) 
      (auxtr : auxiliary_trace LM) 
      (c2 : cfg Λ) (fs : gmap (fmrole iM) nat) (ζ : locale Λ)
    `(dom fs ≠ ∅)
    `(locale_step (trace_last extr) (Some ζ) c2) : iProp Σ :=
   (
        has_fuels ζ (S <$> fs) -∗
           model_state_interp (trace_last extr).1 (trace_last auxtr) ==∗
           ∃ (δ2 : LM) (ℓ : mlabel LM),
             ⌜labels_match (Some ζ) ℓ (LM := LM)
              ∧ valid_state_evolution_fairness (extr :tr[ Some ζ ]: c2)
                  (auxtr :tr[ ℓ ]: δ2)⌝ ∗
             has_fuels ζ (filter (λ '(k, _), k ∈ dom fs ∖ ∅) fs) ∗
             model_state_interp c2.1 δ2)%I. 

    Let update_fork_split_def (R1 R2: gset (fmrole iM)) tp1 tp2
        (fs: gmap (fmrole iM) nat)
        (extr : execution_trace Λ)
        (auxtr: auxiliary_trace LM) ζ efork σ1 σ2
         `(R1 ## R2)
         `(fs ≠ ∅)
         `(R1 ∪ R2 = dom fs)
         `(trace_last extr = (tp1, σ1))
         `(locale_step (tp1, σ1) (Some ζ) (tp2, σ2))
         `((∃ tp1', tp2 = tp1' ++ [efork] ∧ length tp1' = length tp1)): iProp Σ :=
       (
    (* has_fuels_S ζ fs -∗ *)
    has_fuels ζ (S <$> fs) -∗
      model_state_interp (trace_last extr).1 (trace_last auxtr) ==∗
      ∃ δ2, has_fuels (locale_of tp1 efork) (fs ⇂ R2) ∗
            has_fuels ζ (fs ⇂ R1) ∗
            (partial_mapping_is {[ locale_of tp1 efork := ∅ ]} -∗ frag_mapping_is {[ locale_of tp1 efork := ∅ ]}) ∗
            model_state_interp tp2 δ2
        ∧ ⌜valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[Silent_step ζ]: δ2)⌝).


    Let update_step_still_alive_def
      (extr : execution_trace Λ)
      (auxtr: auxiliary_trace LM)
      tp1 tp2 σ1 σ2
      (s1 s2: iM)
      (fs1 fs2: gmap (fmrole iM) nat)
      ρ (δ1 : LM) ζ fr1 fr_stash
      (Einvs: coPset)
    `((live_roles _ s2 ∖ live_roles _ s1) ⊆ fr1)
    `(fr_stash ⊆ dom fs1)
    `((live_roles _ s1) ∩ (fr_stash ∖ {[ ρ ]}) = ∅)
    `(dom fs2 ∩ fr_stash = ∅)
    `(trace_last extr = (tp1, σ1))
    `(trace_last auxtr = δ1)
    `(locale_step (tp1, σ1) (Some ζ) (tp2, σ2))
    `(fmtrans _ s1 (Some ρ) s2)
     `(valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := iLM))
      : iProp Σ :=
    ( has_fuels ζ fs1 -∗ partial_model_is s1 -∗ model_state_interp tp1 δ1 -∗
    partial_free_roles_are fr1
    ={ Einvs }=∗
    ∃ (δ2: LM) ℓ,
      ⌜labels_match (Some ζ) ℓ ∧
       valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[ℓ]: δ2)⌝ ∗
      has_fuels ζ fs2 ∗ partial_model_is s2 ∗ model_state_interp tp2 δ2 ∗
      partial_free_roles_are (fr1 ∖ (live_roles _ s2 ∖ live_roles _ s1) ∪ fr_stash)). 

    Let partial_free_roles_fuels_disj_def n δ fr fs tid: iProp Σ :=
        model_state_interp n δ -∗ partial_free_roles_are fr -∗ has_fuels tid fs -∗ ⌜ fr ## dom fs ⌝.

    Let PMP_def (Einvs: coPset): iProp Σ := □ (
          (∀ extr auxtr c2 fs ζ NE STEP, update_no_step_enough_fuel_def extr auxtr c2 fs ζ NE STEP) ∗         
          (∀ R1 R2 tp1 tp2 fs extr auxtr ζ efork σ1 σ2 DISJ NE DOM EQatp STEP POOL, update_fork_split_def R1 R2 tp1 tp2 fs extr auxtr ζ efork σ1 σ2 DISJ NE DOM EQatp STEP POOL) ∗ 
          (∀ extr auxtr tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ δ1 ζ fr1 fr_stash
             LR STASH NSL NOS2 LAST1 LAST1' STEP STEP' VFM,
              update_step_still_alive_def extr auxtr tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ δ1 ζ fr1 fr_stash Einvs LR STASH NSL NOS2 LAST1 LAST1' STEP STEP' VFM) ∗
          (∀ n δ fr fs tid, partial_free_roles_fuels_disj_def n δ fr fs tid)).  

    Definition PartialModelPredicates Einvs: iProp Σ := PMP_def Einvs. 

    Lemma Build_PartialModelPredicates Einvs: PMP_def Einvs ⊢ PartialModelPredicates Einvs.
    Proof. done. Qed. 

    Global Instance PMP_pers: forall Einvs, Persistent (PartialModelPredicates Einvs). 
    Proof. apply _. Qed. 
    
    (* Doing this _def indirection to provide the "PMP -∗ (property)" lemmas
       while gathering them in one iProp to ease the constructions,
       and make PMP opaque, since its unfold takes too much space *)

    Lemma update_no_step_enough_fuel {Einvs} extr auxtr c2 fs ζ NE STEP: 
      PartialModelPredicates Einvs ⊢ update_no_step_enough_fuel_def extr auxtr c2 fs ζ NE STEP. 
    Proof. by iIntros "(?&?&?&?)". Qed.
    Lemma update_fork_split {Einvs} R1 R2 tp1 tp2 fs extr auxtr ζ efork σ1 σ2 DISJ NE DOM EQatp STEP POOL: 
      PartialModelPredicates Einvs ⊢ update_fork_split_def R1 R2 tp1 tp2 fs extr auxtr ζ efork σ1 σ2 DISJ NE DOM EQatp STEP POOL. 
    Proof. by iIntros "(?&?&?&?)". Qed.
    Lemma update_step_still_alive {Einvs} extr auxtr tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ δ1 ζ fr1 fr_stash LR STASH NSL NOS2 LAST1 LAST1' STEP STEP' VFM:
      PartialModelPredicates Einvs ⊢ update_step_still_alive_def extr auxtr tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ δ1 ζ fr1 fr_stash Einvs LR STASH NSL NOS2 LAST1 LAST1' STEP STEP' VFM.
    Proof. by iIntros "(?&?&?&?)". Qed.
    Lemma partial_free_roles_fuels_disj {Einvs} n δ fr fs tid:
      PartialModelPredicates Einvs ⊢ partial_free_roles_fuels_disj_def n δ fr fs tid.
    Proof. by iIntros "(?&?&?&?)". Qed.

    Global Opaque PartialModelPredicates.

  End PartialModelPredicates.

End PartialOwnership.


Section model_state_lemmas.
  Context `{LM: LiveModel Λ M}.
  Context `{Countable (locale Λ)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  (* TODO: decide what to do with notations *)
  Notation "tid ↦M R" := (frag_mapping_is {[ tid := R ]}) (at level 33).
  Notation "tid ↦m ρ" := (frag_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
  Notation "ρ ↦F f" := (frag_fuel_is {[ ρ := f ]}) (at level 33).


  (* TODO: upstream *)
  Lemma gmap_disj_op_union:
  ∀ {K : Type} {EqDecision0 : EqDecision K} 
    {H : Countable K} {A : cmra} (m1 m2 : gmap K A),
    map_disjoint m1 m2 -> m1 ⋅ m2 = m1 ∪ m2. 
  Proof using. 
    intros. apply map_eq. intros.
    rewrite lookup_op lookup_union.
    destruct (m1 !! i) eqn:L1, (m2 !! i) eqn:L2; try done.
    eapply map_disjoint_spec in H1; done.
  Qed.     

  Lemma empty_frag_free_roles:
    ⊢ |==> frag_free_roles_are ∅.
  Proof. iApply own_unit. Qed. 

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
