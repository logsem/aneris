From iris.algebra Require Import gmap gset.
From iris.proofmode Require Import tactics.

(* TODO: move these lemmas to appropriate places *)

Lemma gmap_disj_op_union:
  ∀ {K : Type} {EqDecision0 : EqDecision K} 
    {H : Countable K} {A : cmra} (m1 m2 : gmap K A),
    map_disjoint m1 m2 -> m1 ⋅ m2 = m1 ∪ m2. 
Proof using. 
  intros. apply map_eq. intros.
  rewrite lookup_op lookup_union.
  destruct (m1 !! i) eqn:L1, (m2 !! i) eqn:L2; try done.
  eapply map_disjoint_spec in H0; done.
Qed.     

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

  (* TODO: upstream *)
  Lemma big_opM_fmap_singletons
    {B: cmra} (m : gmap K A) (f: A -> B)
    (LE: LeibnizEquiv B):
    ([^ op map] k↦x ∈ m, f <$> {[k := x]}) = (f <$> m: gmap K B).
  Proof.
    intros. pattern m. apply map_ind.
    { rewrite big_opM_empty fmap_empty. done. }
    intros. 
    rewrite insert_union_singleton_l.
    apply leibniz_equiv.
    rewrite big_opM_union.
    2: { by apply map_disjoint_singleton_l_2. }
    rewrite H1. rewrite big_opM_singleton.
    rewrite map_fmap_union. rewrite !map_fmap_singleton /=.
    apply leibniz_equiv_iff. apply gmap_disj_op_union.
    apply map_disjoint_singleton_l_2. rewrite lookup_fmap H0. done.
  Qed.

  (* TODO: upstream *)
  Lemma big_opM_insert_delete':
  ∀ {M : ofe} {o : M → M → M} {Monoid0 : Monoid o}
    {B : Type} 
    (f : K → B → M) (m : gmap K B) (i : K) (x : B),
    m !! i = Some x ->
    ([^ o map] k↦y ∈ m, f k y)
    ≡ o (f i x) ([^ o map] k↦y ∈ delete i m, f k y).
  Proof.
    intros. rewrite -big_opM_insert_delete.
    symmetry. eapply big_opM_insert_override; eauto.
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
  Proof.    intros Hinv Hζ Hρ Hζ' Hρ'.
    assert (M !! ρ = Some ζ); first by apply Hinv; eexists; done.
    assert (M !! ρ = Some ζ'); first by apply Hinv; eexists; done.
    congruence.
  Qed.

  Lemma maps_inverse_match_exact (v: V) (S: gset K):
    maps_inverse_match (gset_to_gmap v S) {[v := S]}.
  Proof.
    red. intros. rewrite lookup_gset_to_gmap_Some. split.
    - intros [? ->]. eexists. split; eauto. apply lookup_singleton.
    - intros [? [[? ->]%lookup_singleton_Some ?]]. done.
  Qed.    
  
  Lemma maps_inverse_match_uniq1 (m1 m2: gmap K V) (m': gmap V (gset K))
    (M1: maps_inverse_match m1 m') (M2: maps_inverse_match m2 m'):
    m1 = m2.
  Proof.
    red in M1, M2. apply map_eq. intros.
    destruct (m1 !! i) eqn:L1.
    - pose proof (proj1 (M1 _ _) L1) as EQ.
      pose proof (proj2 (M2 _ _) EQ).
      congruence.
    - destruct (m2 !! i) eqn:L2; [| done].
      pose proof (proj1 (M2 _ _) L2) as EQ.
      pose proof (proj2 (M1 _ _) EQ).
      congruence.
  Qed.

  Lemma maps_inverse_match_subseteq (m1 m2: gmap K V) (m1' m2': gmap V (gset K))
    (M1: maps_inverse_match m1 m1') (M2: maps_inverse_match m2 m2')
    (SUB: dom m1' ⊆ dom m2')
    (INCL: forall v S1 S2, m1' !! v = Some S1 -> m2' !! v = Some S2 -> S1 ⊆ S2):
    m1 ⊆ m2.
  Proof.
    red in M1, M2. apply map_subseteq_spec. intros.
    specialize (proj1 (M1 _ _) H1) as [? [L1 ?]]. 
    apply M2.
    specialize (SUB x (elem_of_dom_2 _ _ _ L1)).
    apply elem_of_dom in SUB as [? ?].
    eexists. split; eauto. set_solver.
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

(* TODO: upstream *)
(* Lemma not_elem_of_equiv_not_empty_L: *)
(* ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} *)
(*   {H2 : Union C}, *)
(*   SemiSet A C → LeibnizEquiv C → *)
(*   ∀ X : C, X ≠ ∅ ↔ (exists x : A, x ∈ X). *)
Lemma gset_not_elem_of_equiv_not_empty_L:
  ∀ {A : Type} `{Countable A},
  ∀ (X : gset A), X ≠ ∅ ↔ (exists x : A, x ∈ X).
Proof.
  intros. split.
  - by apply set_choose_L.
  - set_solver. 
Qed. 

