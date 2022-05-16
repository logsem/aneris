From Coq Require Import ssreflect.
From stdpp Require Import namespaces countable list.

(** List difference. *)

Definition list_minus {A:Type} `{EqDecision A} (l1 l2 : list A) :=
  (max_prefix l1 l2).1.1.

Lemma list_minus_nil_r {A:Type} `{EqDecision A} (l : list A) :
  list_minus l [] = l.
Proof. by destruct l. Qed.

Lemma list_minus_nil_l {A:Type} `{EqDecision A} (l : list A) :
  list_minus [] l = [].
Proof. by destruct l. Qed.

Lemma list_minus_prefix_app {A : Type} `{EqDecision A}
      (l1 l2 l3 : list A) :
  l1 `prefix_of` l2 →
  list_minus (l2 ++ l3) l1 = (list_minus l2 l1) ++ l3.
Proof.
  revert l1.
  induction l2 as [|x l2 IHl2]; intros l1 Hprefix.
  - apply prefix_nil_inv in Hprefix. rewrite Hprefix.
    by rewrite list_minus_nil_r.
  - destruct l1 as [|y l1]; [by rewrite list_minus_nil_r|].
    rewrite /list_minus. simpl.
    case_decide; [|by apply prefix_cons_inv_1 in Hprefix].
    subst. apply IHl2.
    by eapply prefix_cons_inv_2.
Qed.

Lemma list_minus_prefix_length {A : Type} `{EqDecision A}
      (l1 l2 : list A) :
  l1 `prefix_of` l2 → length (list_minus l2 l1) = length l2 - length l1.
Proof.
  generalize dependent l1.
  induction l2 as [|x l2 IHl2]; [done|]; intros l1 Hprefix.
  destruct l1; [done|].
  rewrite /list_minus. simpl.
  case_decide; [|by apply prefix_cons_inv_1 in Hprefix].
  subst. apply IHl2.
  by eapply prefix_cons_inv_2.
Qed.

Lemma list_minus_id_nil {A : Type} `{EqDecision A} (l : list A) :
  list_minus l l = [].
Proof. induction l; [done|]. rewrite /list_minus /=. by case_decide. Qed.

Lemma list_minus_cons {A : Type} `{EqDecision A} x (l1 l2 : list A) :
  list_minus l2 l1 = list_minus (x::l2) (x::l1).
Proof. rewrite /list_minus. destruct l1 as [|y l1]; simpl; by case_decide. Qed.

Lemma list_minus_alt {A : Type} `{EqDecision A} (l1 l2 : list A) :
  l1 `prefix_of` l2 →
  list_minus l2 l1 = drop (length l1) l2.
Proof.
  revert l2.
  induction l1 as [|x l1 IHl1]; intros l2 Hprefix.
  { rewrite list_minus_nil_r. done. }
  destruct l2 as [|y l2]; [done|].
  assert (x = y) as -> by by eapply prefix_cons_inv_1.
  rewrite -list_minus_cons. apply IHl1. by eapply prefix_cons_inv_2.
Qed.
