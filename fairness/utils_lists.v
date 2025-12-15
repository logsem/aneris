From stdpp Require Import base.
From iris.proofmode Require Import tactics.

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

(* TODO: find existing*)
Lemma nth_error_lookup {A: Type} (l: list A) i:
  nth_error l i = l !! i.
Proof using.
  rewrite /lookup. 
  generalize dependent i. induction l.
  { simpl. intros. by destruct i. }
  intros. destruct i; try done. simpl. eauto.
Qed.

Lemma zip_lookup_Some_1 {A B: Type} (la: list A) (lb: list B) i a b:
  zip la lb !! i = Some (a, b) -> la !! i = Some a /\ lb !! i = Some b.
Proof using.
  clear. 
  revert la lb a b. induction i.
  { intros. destruct la, lb; simpl in *; try discriminate. set_solver. }
  intros. destruct la, lb; simpl in *; try discriminate.
  apply IHi in H. done.
Qed.

Lemma foldl_foldr_rev {A B : Type} (f : B → A → B) (b : B) (la : list A):
  foldl f b la = foldr (flip f) b (rev la). 
Proof using.
  generalize dependent b. induction la.
  { done. }
  simpl. intros. rewrite IHla.
  by rewrite foldr_app.
Qed.

