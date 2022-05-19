From stdpp Require Import tactics sets list.

(** TODO: Get all of this merged into stdpp *)

(* About [last] *)
Lemma last_app_cons {A : Type} (xs ys : list A) x :
  last (xs ++ x :: ys) = last (x :: ys).
Proof. induction xs as [|y xs IHxs]; [done|by destruct xs]. Qed.

Lemma last_Some_elem_of {A : Type} (l : list A) x :
  last l = Some x → x ∈ l.
Proof.
  intros Hl.
  induction l as [|y l IHl] using rev_ind; [done|].
  rewrite last_snoc in Hl. inversion Hl as [[Heq]].
  apply elem_of_app. right. by apply elem_of_list_singleton.
Qed.

Lemma last_cons_ne {A:Type} (l : list A) x y :
  x ≠ y → last (x :: l) = Some y → last l = Some y.
Proof. rewrite last_cons. destruct (last l); [done|naive_solver]. Qed.

(* About [prefix_of] *)
Lemma elem_of_prefix {A:Type} (l1 l2 : list A) x :
  l1 `prefix_of` l2 → x ∈ l1 → x ∈ l2.
Proof. intros [l' ->] Hin. apply elem_of_app. by left. Qed.

Lemma prefix_sync_eq {A:Type} k1 k2 (l1 l2 l1' l2' : list A) :
  k1 ∉ l2 → k2 ∉ l1 →
  (l1 ++ [k1] ++ l1') `prefix_of` (l2 ++ [k2] ++ l2') →
  l1 = l2.
Proof.
  intros Hk1 Hk2 Hl.
  generalize dependent l1.
  induction l2 as [|x l2 IHl2]; intros l1 Hk2 Hl.
  - destruct l1 as [|y l1].
    + done.
    + assert (y = k2).
      { by eapply prefix_cons_inv_1. }
      assert (k2 ≠ y).
      { set_solver. }
      done.
  - destruct l1 as [|y l1].
    + assert (x = k1) as ->.
      { symmetry. by eapply prefix_cons_inv_1. }
      set_solver.
    + assert (x = y) as ->.
      { symmetry. by eapply prefix_cons_inv_1. }
      subst.
      assert (l1 = l2) as ->.
      { eapply IHl2.
        { set_solver. }
        { set_solver. }
        simpl in *.
        by eapply prefix_cons_inv_2. }
      done.
Qed.

Lemma prefix_app_inv {A : Type} (xs ys zs : list A) :
  (xs ++ ys) `prefix_of` (xs ++ zs) → ys `prefix_of` zs.
Proof.
  intros Hperm.
  induction xs.
  - done.
  - simpl in *.
    apply IHxs.
    by eapply prefix_cons_inv_2.
Qed.

(* About [delete] *)
Lemma elem_of_list_delete {A : Type} x i (l : list A) :
  x ∈ delete i l → x ∈ l.
Proof.
  revert i.
  induction l as [|z l IHl]; [done|]; intros i Hin.
  destruct i as [|i]; [by right|].
  apply elem_of_cons in Hin.
  destruct Hin as [-> | Hin]; [by left|].
  right. by eapply IHl.
Qed.

(* About [sublist_of] *)
Lemma elem_of_sublist {A : Type} x (l1 l2 : list A) :
  x ∈ l1 → l1 `sublist_of` l2 → x ∈ l2.
Proof.
  intros Hin Hle.
  rewrite sublist_alt in Hle.
  destruct Hle as [l' ->].
  induction l' as [|y l' IHl']; [done|].
  apply IHl'.
  by eapply elem_of_list_delete.
Qed.

Lemma sublist_filter {A : Type} `{!EqDecision A} P `{! ∀ x : A, Decision (P x)}
      (xs : list A) :
  filter P xs `sublist_of` xs.
Proof.
  induction xs; [done|].
  rewrite filter_cons. destruct (decide (P a)).
  { by apply sublist_skip. }
  by apply sublist_cons.
Qed.

Lemma sublist_of_split {A} (l1 l2 l : list A) x :
  l1 ++ [x] ++ l2 `sublist_of` l →
  ∃ l1' l2', l = l1' ++ [x] ++ l2' ∧ l1 `sublist_of` l1' ∧ l2 `sublist_of` l2'.
Proof.
  intros Hl.
  apply sublist_app_l in Hl.
  destruct Hl as [k1 [k2 [-> [Hle1 Hle2]]]].
  apply sublist_cons_l in Hle2.
  destruct Hle2 as [k1' [k2' [-> Hle3]]].
  simpl in *.
  exists (k1++k1'), k2'.
  split. rewrite app_assoc. naive_solver.
  split; [|done].
  rewrite sublist_app_r.
  exists l1, [].
  split; [by rewrite app_nil_r|].
  split; [done|].
  apply sublist_nil_l.
Qed.

(* About [filter] *)
Lemma filter_nil_notin {A : Type} `{!EqDecision A} P `{! ∀ x : A, Decision (P x)}
      (xs : list A) (x : A) :
  filter P xs = [] → P x → x ∉ xs.
Proof.
  intros Hfilter HP Hin.
  induction xs.
  - set_solver.
  - destruct (decide (x = a)).
    { subst. rewrite filter_cons_True in Hfilter; done. }
    apply elem_of_cons in Hin.
    destruct Hin as [Heq|Hin]; [done|].
    simpl in Hfilter.
    rewrite filter_cons in Hfilter.
    destruct (decide (P a)); [done|].
    apply IHxs; done.
Qed.

(* About [filter] with [last] *)
Lemma last_filter_postfix `{!EqDecision A} P
      `{! ∀ x : A, Decision (P x)} l x :
  last (filter P l) = Some x →
  ∃ l1 l2, l = l1 ++ [x] ++ l2 ∧ Forall (λ z, ¬ (P z)) l2.
Proof.
  intros Hl.
  assert (P x) as HPx.
  { by eapply elem_of_list_filter, last_Some_elem_of. }
  pose proof (elem_of_list_split_r l x) as (l1&l2&->&Hinl2).
  { by eapply elem_of_list_filter, last_Some_elem_of. }
  exists l1, l2.
  split; [done|].
  induction l2 as [|z l2 IHl2]; [done|].
  apply not_elem_of_cons in Hinl2. destruct Hinl2 as [Hneq Hnin].
  rewrite filter_app, filter_cons_True, filter_cons, last_app_cons in Hl; [|done].
  destruct (decide (P z)).
  + rewrite last_cons_cons in Hl.
    assert (last (filter P l2) = Some x) as Helemof.
    { destruct (filter P l2); [by inversion Hl|done]. }
    apply last_Some_elem_of in Helemof.
    pose proof (elem_of_list_filter P l2 x) as [Helemof' _].
    specialize (Helemof' Helemof).
    by destruct Helemof' as [_ Helemof'].
  + apply Forall_cons. split; [done|].
    eapply IHl2; [|done].
    by rewrite filter_app, filter_cons_True, last_app_cons.
Qed.

(* About [list_subseteq] (NB: we use none of these) *)
Lemma list_subseteq_cons {A : Type} x (l1 l2 : list A) :
  l1 ⊆ l2 → x :: l1 ⊆ x :: l2 .
Proof.
  intros Hin y Hy%elem_of_cons.
  destruct Hy as [-> | Hy]; [by left|]. right. by apply Hin.
Qed.

Lemma list_subseteq_cons_r {A : Type} x (l1 l2 : list A) :
  l1 ⊆ l2 → l1 ⊆ x :: l2 .
Proof. intros Hin y Hy. right. by apply Hin. Qed.

Lemma list_delete_subseteq {A : Type} i (l : list A) :
  delete i l ⊆ l.
Proof.
  revert i.
  induction l; intros i.
  - done.
  - destruct i as [|i].
    + simpl. apply list_subseteq_cons_r. done.
    + simpl. apply list_subseteq_cons. done.
Qed.

Lemma filter_subseteq {A : Type} `{!EqDecision A} P `{! ∀ x : A, Decision (P x)}
      (xs : list A) :
  filter P xs ⊆ xs.
Proof.
  induction xs; [done|].
  rewrite filter_cons. destruct (decide (P a)); set_solver.
Qed.
