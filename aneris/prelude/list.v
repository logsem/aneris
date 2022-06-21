From Coq.ssr Require Import ssreflect.
From stdpp Require Import list gmap.

Definition flatten {A : Type} (l : list (list A)) : list A := fold_right (λ l1 l2, l1 ++ l2) [] l.

Lemma elem_of_flatten {A} l l' :
  l' ∈ flatten l ↔ ∃ l'' : list A, l' ∈ l'' ∧ l'' ∈ l.
Proof.
  revert l'; induction l as [|a l IHl]; simpl.
  - intros ?; split.
    + intros ?%elem_of_nil; done.
    + intros (? & ? & ?%elem_of_nil); done.
  - intros l'; split.
    + intros [Hl'|Hl']%elem_of_app.
      * exists a; split; first done. apply elem_of_cons; auto.
      * apply IHl in Hl' as (?&?&?).
        eexists _; split; first done. apply elem_of_cons; auto.
    + intros (l'' & Hl'l'' & [->|Hl'']%elem_of_cons).
      * apply elem_of_app; auto.
      * apply elem_of_app; right. apply IHl; eauto.
Qed.

Lemma filter_cons_inv {A} (P : A → Prop) `{!∀ x, Decision (P x)} l x l':
  filter P l = x :: l' → ∃ l1 l2, l = l1 ++ x :: l2 ∧ ∀ z, z ∈ l1 → ¬ P z.
Proof.
  induction l as [|a l IHl]; first done.
  destruct (decide (P a)).
  - rewrite filter_cons_True; first done.
    intros ?; simplify_eq.
    exists [], l; split; first done.
    setoid_rewrite elem_of_nil; done.
  - rewrite filter_cons_False; first done.
    intros (l1 & l2 & -> & Hfa)%IHl.
    eexists (a :: _), _; split; first done.
    intros ?; rewrite elem_of_cons; intros [->|]; auto.
Qed.
Lemma filter_list_extract_first2 {A} (P : A → Prop) `{!∀ x, Decision (P x)} l x y l':
  filter P l = x :: y :: l' → ∃ i j, i < j ∧ l !! i = Some x ∧ l !! j = Some y ∧ P x ∧ P y.
Proof.
  intros Heq.
  destruct (filter_cons_inv _ _ _ _ Heq) as (l1 & l2 & -> & Hfa).
  rewrite filter_app in Heq.
  destruct (filter P l1) as [|b] eqn:Hl1; last first.
  { exfalso; apply (Hfa b); eapply elem_of_list_filter; erewrite Hl1; apply elem_of_cons; auto. }
  simpl in *.
  assert (P x).
  { eapply elem_of_list_filter; erewrite Heq; apply elem_of_cons; auto. }
  rewrite filter_cons_True in Heq; first done.
  simplify_eq.
  destruct (filter_cons_inv _ _ _ _ Heq) as (l3 & l4 & -> & Hfa').
  assert (P y).
  { eapply elem_of_list_filter; erewrite Heq; apply elem_of_cons; auto.  }
  exists (length l1), (length l1 + S (length l3)); split_and!; [lia| | |done|done].
  - rewrite lookup_app_r; first done. rewrite Nat.sub_diag; done.
  - rewrite lookup_app_r; first lia.
    rewrite minus_plus /=.
    rewrite lookup_app_r; first done. rewrite Nat.sub_diag; done.
Qed.

Lemma prefix_Some_None {A} (P : A → Prop) `{!∀ x, Decision (P x)} xs ys zs x :
  last (filter P xs) = Some x →
  last (filter P ys) = None →
  xs `prefix_of` ys ++ zs →
  ys `prefix_of` xs.
Proof.
  intros Hsome Hnone Hprefix.
  rewrite last_None in Hnone.
  generalize dependent xs.
  induction ys as [|y ys]; intros xs Hsome Hprefix.
  { by apply prefix_nil. }
  destruct xs as [|x' xs]; [done|].
  assert (y = x') as <-.
  { by apply prefix_cons_inv_1 in Hprefix. }
  apply prefix_cons.
  rewrite filter_cons in Hnone.
  apply prefix_cons_inv_2 in Hprefix.
  rewrite filter_cons in Hsome.
  apply IHys; [by destruct (decide (P y))|by destruct (decide (P y))|done].
Qed.

Lemma prefix_cons_nil {A:Type} (xs : list A) y ys :
  xs ≠ [] →
  xs `prefix_of` y :: ys →
  [y] `prefix_of` xs.
Proof.
  intros Hneq Hprefix.
  destruct xs; [done|].
  apply prefix_cons_inv_1 in Hprefix.
  rewrite Hprefix.
  by apply prefix_cons, prefix_nil.
Qed.

Lemma last_filter_app_r {A} (P : A → Prop) `{!∀ x, Decision (P x)} xs ys x :
  last (filter P (xs ++ ys)) = Some x →
  last (filter P xs) = None →
  last (filter P ys) = Some x.
Proof.
  intros Hsome Hnone%last_None.
  by rewrite filter_app Hnone in Hsome.
Qed.

Lemma prefix_split_eq {A} (P : A → Prop) `{!∀ x, Decision (P x)} xs ys zs x y :
  last (filter P xs) = Some x →
  last (filter P ys) = None →
  last (filter P zs) = None →
  xs `prefix_of` ys ++ [y] ++ zs →
  x = y.
Proof.
  intros Hsome Hnone1 Hnone2 Hprefix.
  assert (ys `prefix_of` xs) as [k ->].
  { by eapply prefix_Some_None. }
  apply prefix_app_inv in Hprefix.
  apply last_filter_app_r in Hsome; [|done].
  assert ([y] `prefix_of` k) as [k' ->].
  { eapply prefix_cons_nil; [|done]. by intros ->. }
  rewrite filter_app in Hsome.
  rewrite last_None in Hnone2.
  apply prefix_app_inv in Hprefix.
  destruct Hprefix as [k'' ->].
  rewrite filter_app in Hnone2.
  apply app_eq_nil in Hnone2.
  destruct Hnone2 as [Hnone2 _].
  rewrite Hnone2 in Hsome.
  rewrite filter_cons in Hsome.
  destruct (decide (P y)); [|done].
  simpl in *. by simplify_eq.
Qed.

Lemma elem_of_last_filter_exists_Some
      {A} `{EqDecision A} (P : A → Prop) `{!∀ x, Decision (P x)} xs x y :
  last (filter P xs) = x →
  y ∈ xs → P y →
  ∃ x', last (filter P xs) = Some x'.
Proof.
  intros Hlast Hin HPy.
  induction xs as [|z xs IHxs]; [by set_solver|].
  destruct (decide (P z)) as [HPz|HPz].
  - rewrite filter_cons_True; [done|].
    assert (last (filter P xs) = None ∨
                                   ∃ x', last (filter P xs) = Some x') as Hfilter.
    { by destruct (last (filter P xs)); [right; eexists _|left]. }
    destruct Hfilter as [Hnone|[x' Hsome]].
    + exists z. rewrite last_None in Hnone. by rewrite Hnone.
    + exists x'. rewrite last_cons. by rewrite Hsome.
  - rewrite filter_cons_False; [done|].
    rewrite filter_cons_False in Hlast; [done|].
    assert (y ≠ z) as Hneq.
    { intros Heq. by simplify_eq. }
    apply elem_of_cons in Hin.
    destruct Hin as [Hin|Hin]; [done|by apply IHxs].
Qed.
