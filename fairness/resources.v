From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import utils fairness fuel. 

Class fairnessGpreS `{Countable G} `(LM: LiveModel G M LSI) Σ := {   
  fairnessGpreS_model :> inG Σ (authUR (optionR (exclR (ModelO M))));
  fairnessGpreS_model_mapping :> inG Σ (authUR (gmapUR G (exclR (gsetR (RoleO M)))));
  fairnessGpreS_model_fuel :> inG Σ (authUR (gmapUR (RoleO M) (exclR natO)));
  fairnessGpreS_model_free_roles :> inG Σ (authUR (gset_disjUR (RoleO M)));
}.

Class fairnessGS `{Countable G} `(LM : LiveModel G M LSI) Σ := FairnessGS {
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

(* Global Arguments fairnessGS {_ _ _} LM Σ {_ _}. *)
(* Global Arguments FairnessGS {_ _ _} LM Σ {_ _ _} _ _ _. *)
(* Global Arguments fairness_model_name {_ _ _ LM Σ _ _} _. *)
(* Global Arguments fairness_model_mapping_name {G M LSI LM Σ _ _} _ : assert. *)
(* Global Arguments fairness_model_fuel_name {G M LSI LM Σ _ _} _ : assert. *)
(* Global Arguments fairness_model_free_roles_name {G M LSI LM Σ _ _} _ : assert. *)
Global Arguments fairnessGS {_ _ _ _ _} LM Σ. 
Global Arguments FairnessGS {_ _ _ _ _} LM Σ _ _ _.
Global Arguments fairness_model_name {_ _ _ _ _ LM Σ} _.
Global Arguments fairness_model_mapping_name {G _ _ M LSI LM Σ} _ : assert.
Global Arguments fairness_model_fuel_name {G _ _ M LSI LM Σ} _ : assert.
Global Arguments fairness_model_free_roles_name {G _ _ M LSI LM Σ} _ : assert.

Definition fairnessΣ G M `{Countable G} : gFunctors := #[
   GFunctor (authUR (optionUR (exclR (ModelO M))));
   GFunctor (authUR (gmapUR G (exclR (gsetR (RoleO M)))));
   GFunctor (authUR (gmapUR (RoleO M) (exclR natO)));
   GFunctor (authUR (gset_disjUR (RoleO M)))
].

Global Instance subG_fairnessGpreS {Σ} `{Countable G} `{LM : LiveModel G M LSI} :
  subG (fairnessΣ G M) Σ -> fairnessGpreS LM Σ.
Proof. solve_inG. Qed. 

Notation "f ⇂ R" := (filter (λ '(k,v), k ∈ R) f) (at level 30).




Section model_state_interp.
  Context `{Countable G}.
  Context `{LM: LiveModel G M LSI}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  Notation Role := (M.(fmrole)).

  Definition auth_fuel_is (F: gmap Role nat): iProp Σ :=
    own (fairness_model_fuel_name fG)
        (● (fmap (λ f, Excl f) F : ucmra_car (gmapUR (RoleO M) (exclR natO)))).

  Definition frag_fuel_is (F: gmap Role nat): iProp Σ :=
    own (fairness_model_fuel_name fG)
        (◯ (fmap (λ f, Excl f) F : ucmra_car (gmapUR (RoleO M) (exclR natO)))).

  Definition auth_mapping_is (m: gmap G (gset Role)): iProp Σ :=
    own (fairness_model_mapping_name fG)
        (● ( (fmap (λ (f: gset M.(fmrole)), Excl f) m) :
              ucmra_car (gmapUR _ (exclR (gsetR (RoleO M))))
        )).

  Definition frag_mapping_is (m: gmap G (gset Role)): iProp Σ :=
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

  (* Global Instance ActualOwnershipPartialPre: *)
  (*   @PartialModelPredicatesPre G _ _ Σ M.  *)
  (* Proof. *)
  (*   refine {| *)
  (*       partial_model_is := frag_model_is; *)
  (*       partial_free_roles_are := frag_free_roles_are; *)
  (*       partial_fuel_is := frag_fuel_is; *)
  (*       partial_mapping_is := frag_mapping_is; *)
  (*     |}. *)
  (*   - solve_proper.  *)
  (*   - intros. rewrite /frag_fuel_is. *)
  (*     rewrite map_fmap_union. rewrite -gmap_disj_op_union. *)
  (*     2: { by apply map_disjoint_fmap. } *)
  (*     by rewrite auth_frag_op own_op. *)
  (*   - intros. rewrite /frag_free_roles_are. *)
  (*     rewrite -gset_disj_union; auto.   *)
  (*     by rewrite auth_frag_op own_op. *)
  (*   - iApply empty_frag_free_roles.  *)
  (* Defined.  *)

  (* partial_model_is_Timeless :> forall s, Timeless (partial_model_is s); *)
  (*     partial_fuel_is_Timeless :> forall fs, Timeless (partial_fuel_is fs); *)
  (*     partial_mapping_is_Timeless :> forall rs, Timeless (partial_mapping_is rs); *)
  (*     partial_free_roles_are_Timeless :> forall s, Timeless (partial_free_roles_are s); *)


  (* legacy definitions *)
  (* TODO: remove *)
  Definition partial_model_is := frag_model_is. 
  Definition partial_free_roles_are := frag_free_roles_are.
  Definition partial_fuel_is := frag_fuel_is.
  Definition partial_mapping_is := frag_mapping_is. 
      

  Global Instance partial_free_roles_are_Proper: 
    Proper (equiv ==> equiv) partial_free_roles_are.
  Proof. apply _. Qed.

  Global Instance partial_mapping_is_Proper:
    Proper (equiv ==> equiv) partial_mapping_is.
  Proof. apply _. Qed. 

  Global Instance partial_fuel_is_Proper: 
    Proper (equiv ==> equiv) partial_fuel_is.
  Proof. solve_proper. Qed. 

  Lemma auth_fuel_is_proper
    (x y : gmap (fmrole M) nat):
    x = y ->
    auth_fuel_is x -∗ auth_fuel_is y.
  Proof. by intros ->. Qed.

  Lemma partial_fuels_is_sep: forall fs1 fs2 (DISJ: fs1 ##ₘ fs2),
      partial_fuel_is (fs1 ∪ fs2) ⊣⊢ partial_fuel_is fs1 ∗ partial_fuel_is fs2.
  Proof. 
    intros. rewrite /partial_fuel_is /frag_fuel_is.
    rewrite map_fmap_union. rewrite -gmap_disj_op_union.
    2: { by apply map_disjoint_fmap. }
    by rewrite auth_frag_op own_op.
  Qed. 

  Lemma partial_free_roles_are_sep: forall fr1 fr2 (DISJ: fr1 ## fr2), 
        partial_free_roles_are (fr1 ∪ fr2) ⊣⊢ partial_free_roles_are fr1 ∗ partial_free_roles_are fr2.
  Proof.
    intros. rewrite /partial_free_roles_are /frag_free_roles_are.
    rewrite -gset_disj_union; auto.
    by rewrite auth_frag_op own_op.
  Qed. 

  Lemma partial_free_roles_empty: ⊢ |==> partial_free_roles_are ∅.
  Proof. iApply empty_frag_free_roles. Qed.

  Section has_fuel.
    Notation Role := (M.(fmrole)).

    Notation "tid ↦M R" := (partial_mapping_is {[ tid := R ]}) (at level 33).
    Notation "tid ↦m ρ" := (partial_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
    Notation "ρ ↦F f" := (partial_fuel_is {[ ρ := f ]}) (at level 33).

    Definition has_fuel (ζ: G) (ρ: Role) (f: nat): iProp Σ :=
      ζ ↦m ρ ∗ ρ ↦F f.

    Definition has_fuels (ζ: G) (fs: gmap Role nat): iProp Σ :=
      ζ ↦M dom fs ∗ [∗ set] ρ ∈ dom fs, ∃ f, ⌜fs !! ρ = Some f⌝ ∧ ρ ↦F f.

    (* Context {G: Ofe} *)
    (* Context `{LeibnizEquiv G}. *)

    #[global] Instance has_fuels_proper:
      Proper ((=) ==> (≡) ==> (≡)) (has_fuels).
    Proof. solve_proper. Qed.

    #[global] Instance has_fuels_timeless (ζ: G) (fs: gmap Role nat):
      Timeless (has_fuels ζ fs).
    Proof. rewrite /has_fuels. apply _. Qed.

    Lemma has_fuel_fuels (ζ: G) (ρ: Role) (f: nat):
      has_fuel ζ ρ f ⊣⊢ has_fuels ζ {[ ρ := f ]}.
    Proof.
      rewrite /has_fuel /has_fuels. iSplit.
      - iIntros "[Hζ Hρ]". rewrite dom_singleton_L big_sepS_singleton. iFrame.
        iExists f. iFrame. iPureIntro. by rewrite lookup_singleton.
      - iIntros "(?&H)". rewrite dom_singleton_L big_sepS_singleton. iFrame.
        iDestruct "H" as (?) "H". rewrite lookup_singleton.
        iDestruct "H" as "[% ?]". by simplify_eq.
    Qed.

    Definition has_fuels_S (ζ: G) (fs: gmap Role nat): iProp Σ :=
      has_fuels ζ (fmap S fs).

    Definition has_fuels_plus (n: nat) (ζ: G) (fs: gmap Role nat): iProp Σ :=
      has_fuels ζ (fmap (fun m => n+m) fs).

    Lemma has_fuel_fuels_S (ζ: G) (ρ: Role) (f: nat):
      has_fuel ζ ρ (S f) ⊣⊢ has_fuels_S ζ {[ ρ := f ]}.
    Proof.
      rewrite has_fuel_fuels /has_fuels_S map_fmap_singleton //.
    Qed.

    Lemma has_fuel_fuels_plus_1 (ζ: G) fs:
      has_fuels_plus 1 ζ fs ⊣⊢ has_fuels_S ζ fs.
    Proof.
      rewrite /has_fuels_plus /has_fuels_S.
      do 2 f_equiv.
      intros m m' ->. apply leibniz_equiv_iff. lia.
    Qed.

    Lemma has_fuel_fuels_plus_0 (ζ: G) fs:
      has_fuels_plus 0 ζ fs ⊣⊢ has_fuels ζ fs.
    Proof.
      rewrite /has_fuels_plus /=.  f_equiv. intros ?.
      rewrite lookup_fmap. apply leibniz_equiv_iff.
      destruct (fs !! i) eqn:Heq; rewrite Heq //.
    Qed.

    Lemma has_fuels_plus_split_S n (ζ: G) fs:
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

    Lemma maps_gt_n (fs: gmap Role nat) n:
      (∀ ρ f, fs !! ρ = Some f -> f >= n)%nat ->
      fs = (λ m, n + m)%nat <$> ((λ m, m - n)%nat <$> fs).
    Proof.
      intros Hgt.
      apply map_eq. intros ρ.
      rewrite -map_fmap_compose !lookup_fmap.
      destruct (fs !! ρ) as [f|] eqn:? =>//=. f_equiv.
      assert (f >= n)%nat by eauto.
      apply leibniz_equiv_iff. lia.
    Qed.

    Lemma has_fuels_gt_n (fs: gmap Role nat) (n: nat) (tid: G):
      (∀ ρ f, fs !! ρ = Some f -> f >= n)%nat ->
      has_fuels tid fs ⊣⊢ has_fuels tid ((λ m, n + m)%nat <$> ((λ m, m - n)%nat <$> fs)).
    Proof. intros ?. rewrite {1}(maps_gt_n fs n) //. Qed.

    Lemma has_fuels_gt_1 fs tid:
      (∀ ρ f, fs !! ρ = Some f -> f >= 1)%nat ->
      has_fuels tid fs ⊣⊢ has_fuels_S tid (((λ m, m - 1)%nat <$> fs)).
    Proof. intros ?. by rewrite has_fuels_gt_n //. Qed.

  End has_fuel.

End model_state_interp.

Lemma own_proper `{inG Σ X} γ (x y: X):
  x ≡ y ->
  own γ x -∗ own γ y.
Proof. by intros ->. Qed.

Section model_state_lemmas.
  Context `{Countable G}.
  Context `{LM: LiveModel G M LSI}.
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
    apply -> (@singleton_included_l G) in HA. destruct HA as (R' & HA & Hsub).
    assert (✓ Some R'). by rewrite -HA.
    destruct R' as [R'|]; last done.
    apply Excl_included in Hsub. apply leibniz_equiv in Hsub.
    rewrite Hsub.
    apply leibniz_equiv in HA. rewrite -> lookup_fmap_Some in HA.
    destruct HA as (?&?&?). congruence.
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
    pose proof (ls_mapping_tmap_corr δ) as Hmapinv. 
    rewrite (Hmapinv ρ ζ) HMζ. split.
    - intros (?&?&?). by simplify_eq.
    - intros ?. eexists. split; eauto.
  Qed.

  Lemma has_fuel_in' ζ δ fs:
    has_fuels ζ fs -∗ model_state_interp δ -∗ ⌜ ls_tmap δ !! ζ = Some (dom fs) ⌝.
  Proof.
    unfold model_state_interp, has_fuels, auth_mapping_is, frag_mapping_is.
    iIntros "[Hζ Hfuels] (%FR&Hafuel&Hamapping &HFR&Hamod&Hfr)".
    iCombine "Hamapping Hζ" as "H".
    iDestruct (own_valid with "H") as %Hval. iPureIntro.
    apply auth_both_valid_discrete in Hval as [Hval ?].
    rewrite map_fmap_singleton in Hval.
    apply singleton_included_exclusive_l in Hval =>//; last by typeclasses eauto.
    rewrite -> lookup_fmap, leibniz_equiv_iff in Hval.
    apply fmap_Some_1 in Hval as (R'&HMζ&?). simplify_eq. done. 
  Qed.

  Lemma frag_fuel_included fs FS:
    auth_fuel_is FS -∗ frag_fuel_is fs -∗ ⌜ fs ⊆ FS ⌝.
  Proof.
    iIntros "Hafuel Hfuel".
    iCombine "Hafuel Hfuel" as "H".
    iDestruct (own_valid with "H") as %Hval. iPureIntro.    
    apply auth_both_valid_discrete in Hval as [Hval ?].
    rewrite map_subseteq_spec. iIntros (ρ f Hρ).
    unshelve eapply lookup_included in Hval; [exact ρ| ]. 
    rewrite !lookup_fmap Hρ //= in Hval.
    destruct (FS !! ρ) eqn:LL; rewrite LL in Hval; simpl in Hval. 
    - apply Excl_included in Hval. congruence.
    - red in Hval.
      (* TODO: a canonical way? *)
      destruct Hval as [? ?].
      rewrite Some_op_opM in H1. inversion H1. 
  Qed.

  Lemma frag_fuel_is_big_sepM fs (FSn0: fs ≠ ∅):
       ([∗ map] ρ↦f ∈ fs, frag_fuel_is {[ρ := f]}) ⊣⊢ frag_fuel_is fs.
  Proof.
    rewrite /frag_fuel_is.
    rewrite -big_opM_own; [| done].
    rewrite -big_opM_auth_frag.
    iApply own.own_proper. f_equiv.
    by rewrite big_opM_fmap_singletons.
  Qed.

  Lemma frag_mapping_is_big_sepM m (Mn0: m ≠ ∅):
       ([∗ map] τ↦R ∈ m, frag_mapping_is {[τ := R]}) ⊣⊢ frag_mapping_is m.
  Proof.
    rewrite /frag_mapping_is.
    rewrite -big_opM_own; [| done].
    rewrite -big_opM_auth_frag.
    iApply own.own_proper. f_equiv.
    by rewrite big_opM_fmap_singletons. 
  Qed.


  Lemma has_fuel_fuel ζ δ fs:
    has_fuels ζ fs -∗ model_state_interp δ -∗ 
    ⌜ ∀ ρ, ρ ∈ dom fs -> ls_fuel δ !! ρ = fs !! ρ ⌝.
  Proof.
    unfold has_fuels, model_state_interp, auth_fuel_is.
    iIntros "[Hζ Hfuels] (%FR&Hafuel&Hamapping&HFR&Hamod)" (ρ Hρ).
    iClear "Hζ Hamapping HFR Hamod".
    iDestruct (big_sepS_delete _ _ ρ with "Hfuels") as "[(%f&%Hfs&Hfuel) _]" =>//.
    iPoseProof (frag_fuel_included with "Hafuel Hfuel") as "%INCL".    
    iPureIntro. rewrite Hfs. 
    eapply lookup_weaken; [| apply INCL].
    by rewrite lookup_singleton. 
  Qed.

  Lemma frag_free_roles_fuels_disj: forall δ fr fs tid,
        model_state_interp δ -∗ frag_free_roles_are fr -∗ 
        has_fuels tid fs -∗
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
      destruct (fs !! ρ) eqn:Hfs; inversion Heq as [A S D J Habs|A Habs];
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

End model_state_lemmas.

Section adequacy.
  Context `{Countable G}.
  Context `{LM: LiveModel G M LSI}.
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

  Lemma model_mapping_init' (tmap: gmap G (gset (fmrole M))):
    ⊢ |==> ∃ γ,
        own (A := authUR (gmapUR _ (exclR (gsetR (RoleO M))))) γ
            (● (Excl <$> tmap) ⋅ ◯ (Excl <$> tmap) ).
  Proof.
    iMod (own_alloc (● (Excl <$> tmap) ⋅ ◯ _: authUR (gmapUR _ _))) as (γ) "[Hfl Hfr]".
    { apply auth_both_valid_discrete. split; [reflexivity|].
      intros i. rewrite lookup_fmap. by destruct lookup. }
    iExists _. by iSplitL "Hfl".
  Qed.  

  Lemma model_mapping_init (s0: M) (ζ0: G):
    ⊢ |==> ∃ γ,
        own (A := authUR (gmapUR _ (exclR (gsetR (RoleO M))))) γ
            (● ({[ ζ0 :=  Excl (M.(live_roles) s0) ]}) ⋅
               ◯ ({[ ζ0 :=  Excl (M.(live_roles) s0) ]})).  
  Proof.
    rewrite -map_fmap_singleton. iApply model_mapping_init'.
  Qed.

  Lemma model_fuel_init' (F: gmap (fmrole M) nat):
    ⊢ |==> ∃ γ,
        own (A := authUR (gmapUR (RoleO M) (exclR natO))) γ
            (● (Excl <$> F) ⋅ (◯ (Excl <$> F))).
  Proof.
    iMod (own_alloc
            ((● (Excl <$> F) ⋅ (◯ (Excl <$> F))): authUR (gmapUR (RoleO M) (exclR natO)))) as (γ) "[H1 H2]".
    { apply auth_both_valid_discrete. split; [reflexivity| ].
      intros i. rewrite lookup_fmap. by destruct lookup. } 
    iExists _. by iSplitL "H1".
  Qed.

  Lemma model_fuel_init (s0: M):
    ⊢ |==> ∃ γ,
        own (A := authUR (gmapUR (RoleO M) (exclR natO))) γ
            (● gset_to_gmap (Excl (LM.(lm_fl) s0)) (M.(live_roles) s0)  ⋅
               (◯ gset_to_gmap (Excl (LM.(lm_fl) s0)) (M.(live_roles) s0))).
  Proof.
    rewrite -fmap_gset_to_gmap. iApply model_fuel_init'. 
  Qed.

  Lemma model_free_roles_init (FR: gset _):
    ⊢ |==> ∃ γ,
        own (A := authUR (gset_disjUR (RoleO M))) γ (● GSet FR  ⋅ ◯ GSet FR).
  Proof.
    iMod (own_alloc (● GSet FR  ⋅ ◯ GSet FR)) as (γ) "[H1 H2]".
    { apply auth_both_valid_2 =>//. }
    iExists _. by iSplitL "H1".
  Qed.

  Lemma lm_msi_init (δ: LiveState G M LSI) (fr: gset (fmrole M))
    (FR_DISJ: dom (ls_fuel δ) ## fr):
    ⊢ |==> ∃ (fG: fairnessGS LM Σ), 
        model_state_interp δ ∗
        frag_model_is (ls_under δ)∗
        frag_mapping_is (ls_tmap δ) ∗
        frag_fuel_is (ls_fuel δ) ∗
        frag_free_roles_are fr.
  Proof. 
    iMod (model_state_init (ls_under δ)) as (γ_st) "[AUTH_ST FRAG_ST]".
    iMod (model_mapping_init' (ls_tmap δ)) as (γ_map) "[AUTH_MAP FRAG_MAP]".
    iMod (model_fuel_init' (ls_fuel δ)) as (γ_fuel) "[AUTH_FUEL FRAG_FUEL]".
    iMod (model_free_roles_init fr) as (γ_fr) "[AUTH_FR FRAG_FR]".
    iModIntro.
    iExists {| 
        fairness_inG := fG;
        fairness_model_name := γ_st;
        fairness_model_mapping_name := γ_map;
        fairness_model_fuel_name := γ_fuel;
        fairness_model_free_roles_name := γ_fr;
      |}. 
    rewrite /model_state_interp. 
    iFrame. iExists _. iFrame. iPureIntro. set_solver.
  Qed. 

End adequacy.
