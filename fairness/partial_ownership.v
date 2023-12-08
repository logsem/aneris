From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness.heap_lang Require Import heap_lang_defs.
From trillium.fairness Require Import fuel.

Canonical Structure ModelO (Mdl : FairModel) := leibnizO Mdl.
Canonical Structure RoleO (Mdl : FairModel) := leibnizO (Mdl.(fmrole)).

Section PartialOwnership.
  Context `{G: Type}.
  (* Notation GO := (leibnizO G). *)
  Notation GO := G.

  Context `{Countable G}.
  Context {Σ : gFunctors}.
  (* Context {fG: fairnessGS LM Σ}. *)
  (* Context `{invGS Σ}.  *)
  (* Context `{invGS_gen HasNoLc Σ}.  *)
  Context `{iLM: LiveModel G iM iLSI}. (* fuel construction over inner model *)

  (* Canonical Structure GroupRoleO (G: Type) := leibnizO G. *)

  (* TODO: rename *)
  Class PartialModelPredicatesPre := {
      partial_model_is: fmstate iM -> iProp Σ;
      partial_free_roles_are: gset (fmrole iM) → iProp Σ;
      partial_fuel_is: gmap (fmrole iM) nat → iProp Σ;
      partial_mapping_is: gmap GO (gset (fmrole iM)) → iProp Σ;
      
      partial_model_is_Timeless :> forall s, Timeless (partial_model_is s);
      partial_fuel_is_Timeless :> forall fs, Timeless (partial_fuel_is fs);
      partial_mapping_is_Timeless :> forall rs, Timeless (partial_mapping_is rs);
      partial_free_roles_are_Timeless :> forall s, Timeless (partial_free_roles_are s);

      partial_free_roles_are_Proper :> Proper (equiv ==> equiv) partial_free_roles_are;
      partial_mapping_is_Proper :> Proper (equiv ==> equiv) partial_mapping_is;
      partial_fuel_is_Proper :> Proper (equiv ==> equiv) partial_fuel_is;

      (* partial_msi: LiveState Λ iM -> iProp Σ; *)

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

  Section has_fuel.
    Context {PMPP: PartialModelPredicatesPre}.
    (* Context `{Equiv G}. *)
    (* Context `{LeibnizEquiv G}. *)

    Notation Role := (iM.(fmrole)).

    Definition has_fuel (ζ: GO) (ρ: Role) (f: nat): iProp Σ :=
      ζ ↦m ρ ∗ ρ ↦F f.

    Definition has_fuels (ζ: GO) (fs: gmap Role nat): iProp Σ :=
      ζ ↦M dom fs ∗ [∗ set] ρ ∈ dom fs, ∃ f, ⌜fs !! ρ = Some f⌝ ∧ ρ ↦F f.

    (* Context {G: Ofe} *)
    (* Context `{LeibnizEquiv G}. *)

    #[global] Instance has_fuels_proper:
      Proper ((=) ==> (≡) ==> (≡)) (has_fuels).
    Proof. solve_proper. Qed.

    #[global] Instance has_fuels_timeless (ζ: G) (fs: gmap Role nat):
      Timeless (has_fuels ζ fs).
    Proof. rewrite /has_fuels. apply _. Qed.

    Lemma has_fuel_fuels (ζ: GO) (ρ: Role) (f: nat):
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

    (* Context `{Dist G}.  *)
    (* Context `{GM: OfeMixin G}.  *)
    (* Context `{Equivalence G}.  *)

    Lemma has_fuel_fuels_plus_1 (ζ: G) fs:
      has_fuels_plus 1 ζ fs ⊣⊢ has_fuels_S ζ fs.
    Proof.
      rewrite /has_fuels_plus /has_fuels_S.

      do 2 f_equiv.
      intros m m' ->. apply leibniz_equiv_iff. lia.

      (* f_equiv. *)
      (* -  *)
      (*   eapply leibniz_equiv_iff. done. *)
      (*   Unshelve. *)
      (*   red. intros. *)
      (*   assert (Equivalence (@equiv G H0)). *)
      (*   { apply _.  *)
      (*     typeclasses eauto.  *)
      (*   apply _.  *)
      (*   reflexivity. *)
        
      (*   2: apply _.  *)
      (*   done. inversion H0.  *)


      (* (* intros m m' ->. apply leibniz_equiv_iff. lia. *) *)


      (* rewrite /has_fuels_plus /has_fuels_S. *)
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

  End has_fuel.

End PartialOwnership.

Section AuxDefs.
  Context `{Countable G}. 
  Context `{LM: LiveModel G M LSI}.

  Definition valid_new_fuelmap (fs1 fs2: gmap (fmrole M) nat) (s1 s2: M) (ρ: fmrole M) :=
    (ρ ∈ live_roles _ s2 -> oleq (fs2 !! ρ) (Some (LM.(lm_fl) s2))) ∧
    (ρ ∉ live_roles _ s2 -> ρ ∈ dom fs1 ∩ dom fs2 -> oleq (fs2 !! ρ) (fs1 !! ρ)) ∧
    ρ ∈ dom fs1 ∧
    (forall ρ', ρ' ∈ dom fs2 ∖ dom fs1 -> oleq (fs2 !! ρ') (Some $ LM.(lm_fl) s2)) ∧
    (forall ρ', ρ ≠ ρ' -> ρ' ∈ dom fs1 ∩ dom fs2 -> oless (fs2 !! ρ') (fs1 !! ρ')) ∧
    (dom fs1 ∖ {[ ρ ]}) ∪ (live_roles _ s2 ∖ live_roles _ s1) ⊆ dom fs2 ∧
    dom fs2 ⊆
      (* new roles *) (live_roles _ s2 ∖ live_roles _ s1) ∪
      (* surviving roles *) (live_roles _ s2 ∩ live_roles _ s1 ∩ dom fs1) ∪
      (* already dead *) (dom fs1 ∖ live_roles _ s1) ∪
      (* new deads *) ((live_roles _ s1 ∖ live_roles _ s2) ∩ dom fs1).

  Definition fuel_apply (fs' F: gmap (fmrole M) nat) (LR: gset (fmrole M)):
    gmap (fmrole M) nat :=
    map_imap
      (λ (ρ: fmrole M ) (fold : nat),
       match decide (ρ ∈ dom fs') with
       | left x => fs' !! ρ
       | right _ => F !! ρ
       end) (gset_to_gmap (0%nat) LR).

  Definition update_fuel_resource 
    (* (δ1: LiveState G M LSI) *) (F: gmap (fmrole M) nat)
    (fs1 fs2: gmap (fmrole M) nat): gmap (fmrole M) nat :=
    fuel_apply fs2 F ((dom F ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2)).


  (* (* TODO: refactor this? *) *)
  Definition update_mapping (R: gmap (fmrole M) G) (ζ: G) (fs1 fs2: gmap (fmrole M) nat): gmap (fmrole M) G := 
    map_imap (λ ρ' _, if decide (ρ' ∈ dom R) then R !! ρ' else Some ζ)
      (gset_to_gmap 333 ((dom R ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))). 

  Definition LSI_fuel_independent :=
    forall S R F F',
      LSI S R F -> LSI S R F'.

  Definition fuel_reorder_preserves_LSI :=
    forall S (R R': gmap (fmrole M) G) F F',
      dom R = dom R' ->
      LSI S R F -> LSI S R' F'. 

  Definition fuel_drop_preserves_LSI S (rem: gset (fmrole M)) :=
    forall (R: gmap (fmrole M) G) F F',
      let R' := filter (fun '(k, _) => k ∉ rem) R in
      LSI S R F -> LSI S R' F'. 

  Definition model_step_preserves_LSI s1 ρ s2 fs1 fs2 :=
    forall R g F, LSI s1 R F -> fmtrans M s1 (Some ρ) s2 -> R !! ρ = Some g ->
             LSI s2 (update_mapping R g fs1 fs2) (update_fuel_resource F fs1 fs2). 

End AuxDefs.

Definition LSI_True {G: Type} {M: FairModel}:
  M → gmap (fmrole M) G → gmap (fmrole M) nat → Prop :=
  fun _ _ _ => True.


(* TODO: move to upstream *)
Lemma disjoint_subseteq:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C}
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C},
    `{Set_ A C} → ∀ X1 X2 Y1 Y2: C, X1 ⊆ Y1 -> X2 ⊆ Y2 → Y1 ## Y2 -> X1 ## X2.
Proof. intros. set_solver. Qed.
