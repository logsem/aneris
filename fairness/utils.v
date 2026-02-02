From iris.algebra Require Import gmap gset.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Import quantifiers finitary.
From fairness Require Export utils_coPset utils_logic utils_maps utils_sets utils_relations utils_multisets.


Section Disjoint.

  Lemma disjoint_subseteq:
    ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C}
      {H2 : Union C} {H3 : Intersection C} {H4 : Difference C},
      `{Set_ A C} → ∀ X1 X2 Y1 Y2: C, X1 ⊆ Y1 -> X2 ⊆ Y2 → Y1 ## Y2 -> X1 ## X2.
  Proof. intros. set_solver. Qed.

End Disjoint.


Lemma map_img_sets_split_helper `{Countable K, Countable A} (k: K) (m: gmap K (gset A)):
  flatten_gset $ map_img m = default ∅ (m !! k) ∪ (flatten_gset $ map_img (delete k m)).
Proof using.
  rewrite {1}(map_split m k). rewrite map_img_union_disjoint_L.
  2: { destruct (m !! k) eqn:KTH; simpl. 
       all: apply map_disjoint_dom; set_solver. }
  rewrite flatten_gset_union. f_equal.
  destruct (m !! k) eqn:KTH; simpl.
  - by rewrite map_img_singleton_L flatten_gset_singleton.
  - by rewrite map_img_empty_L flatten_gset_empty.
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



Lemma fmap_flat_map {A B C: Type} (f : A → list B) (g: B -> C) (l : list A):
  g <$> (flat_map f l) = flat_map ((fmap g) ∘ f) l.
Proof.
  induction l; [done| ].
  simpl. rewrite fmap_app. congruence.
Qed.

Lemma concat_NoDup {A: Type} (ll : list (list A)):
  (forall i l, ll !! i = Some l -> NoDup l) ->
  (forall i j li lj, i ≠ j -> ll !! i = Some li -> ll !! j = Some lj -> li ## lj) ->
  NoDup (concat ll).
Proof.
  induction ll.
  { constructor. }
  intros. simpl. apply NoDup_app. repeat split.
  { apply (H 0). done. }
  2: { apply IHll.
       - intros. apply (H (S i)). done.
       - intros. apply (H0 (S i) (S j)); auto. }
  intros. intros [lx [INlx INx]]%elem_of_list_In%in_concat.
  apply elem_of_list_In, elem_of_list_lookup_1 in INlx as [ix IX].
  eapply (H0 0 (S ix)).
  - lia.
  - simpl. reflexivity.
  - simpl. apply IX.
  - eauto.
  - by apply elem_of_list_In.
Qed.


Ltac add_case C name :=
  match goal with
  | |- ?G => assert (C -> G) as name
  end.


Section Arithmetic.

  Lemma even_succ_negb n: Nat.even (S n) = negb $ Nat.even n.
  Proof. by rewrite Nat.even_succ Nat.negb_even. Qed.

  Lemma odd_succ_negb n: Nat.odd (S n) = negb $ Nat.odd n.
  Proof. by rewrite Nat.odd_succ Nat.negb_odd. Qed.

  Lemma even_plus1_negb n: Nat.even (n + 1) = negb $ Nat.even n.
  Proof. by rewrite Nat.add_1_r even_succ_negb. Qed. 

  Lemma odd_plus1_negb n: Nat.odd (n + 1) = negb $ Nat.odd n.
  Proof. by rewrite Nat.add_1_r odd_succ_negb. Qed.

  Lemma even_odd_False n : Nat.even n → Nat.odd n → False.
  Proof.
    intros Heven Hodd. rewrite -Nat.negb_odd in Heven.
    apply Is_true_true_1 in Heven.
    apply Is_true_true_1 in Hodd.
    by rewrite Hodd in Heven.
  Qed.
  
  Lemma even_not_odd n : Nat.even n → ¬ Nat.odd n.
  Proof. intros Heven Hodd. by eapply even_odd_False. Qed.
  
  Lemma odd_not_even n : Nat.odd n → ¬ Nat.even n.
  Proof. intros Heven Hodd. by eapply even_odd_False. Qed.
  
  Lemma even_or_odd n: Nat.even n \/ Nat.odd n.
  Proof. 
    destruct (decide (Nat.even n)) as [| O]; auto.
    apply negb_prop_intro in O. rewrite Nat.negb_even in O. tauto.
  Qed.

End Arithmetic.
