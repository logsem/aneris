From Coq.ssr Require Import ssreflect.
From stdpp Require Import list.

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
