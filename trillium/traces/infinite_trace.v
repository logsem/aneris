From Coq.ssr Require Import ssreflect.
From stdpp Require Import prelude.

Set Default Proof Using "Type".

Delimit Scope inflist_scope with inflist.

CoInductive inflist (A : Type) : Type :=
| infnil
| infcons (x : A) (il : inflist A).

Bind Scope inflist_scope with inflist.

Arguments infnil {_}, _.
Arguments infcons {_} _ _%inflist.

Module InfListNotations.
Notation "[ ]" := infnil (format "[ ]") : inflist_scope.
Notation "[ x ]" := (infcons x infnil) : inflist_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (infcons x (infcons y .. (infcons z nil) ..)) : inflist_scope.

Infix "::" := infcons (at level 60, right associativity) : inflist_scope.
End InfListNotations.

Import InfListNotations.

Section inflist.
  Context {A : Type}.

  Implicit Types il : inflist A.

  Lemma inflist_unfold_fold il :
    il = match il with
         | [] => []
         | a :: il' => a :: il'
         end%inflist.
  Proof. destruct il; trivial. Qed.

  Fixpoint inflist_take (n : nat) (il : inflist A) : list A :=
    match n with
    | O => []
    | S n' =>
      match il with
      | []%inflist => []
      | (a :: il')%inflist => a :: inflist_take n' il'
      end
    end.

  Fixpoint inflist_drop (n : nat) (il : inflist A) : inflist A :=
    match n with
    | O => il
    | S n' =>
      match il with
      | []%inflist => []
      | (a :: il')%inflist => inflist_drop n' il'
      end
    end.

  Lemma inflist_take_add n m il :
    inflist_take (n + m) il = inflist_take n il ++ (inflist_take m (inflist_drop n il)).
  Proof.
    revert m il; induction n; intros m il; first done.
    destruct il; simpl; first by destruct m.
    rewrite IHn //.
  Qed.

  Lemma inflist_drop_add n m il : inflist_drop (n + m) il = (inflist_drop n (inflist_drop m il)).
  Proof.
    revert n il; induction m as [|m IHm]; intros n il.
    { rewrite /= Nat.add_0_r //. }
    rewrite Nat.add_succ_r /=.
    destruct il; last done.
    destruct n; done.
  Qed.

End inflist.

Definition inflist_same_length {A B} (il : inflist A) (il' : inflist B) : Prop :=
  (∀ n, (inflist_drop n il) = [] ↔ (inflist_drop n il') = [])%inflist.

Lemma inflist_same_length_refl {A} (il : inflist A) : inflist_same_length il il.
Proof. done. Qed.

Lemma inflist_same_length_sym {A B} (il : inflist A) (il' : inflist B) :
  inflist_same_length il il' → inflist_same_length il' il.
Proof. firstorder. Qed.

Lemma inflist_same_length_trans {A B C} (il : inflist A) (il' : inflist B) (il'' : inflist C) :
  inflist_same_length il il' → inflist_same_length il' il'' → inflist_same_length il il''.
Proof. firstorder. Qed.

Lemma inflist_same_length_nil {A B}: inflist_same_length (@infnil A) (@infnil B).
Proof. intros []; done. Qed.

Lemma inflist_same_length_nil_inv_l {A B} (x : B) (il : inflist B) :
  ¬ inflist_same_length (@infnil A) (x :: il).
Proof. intros Heq; specialize (Heq 0) as [Heq _]; specialize (Heq eq_refl); done. Qed.
Lemma inflist_same_length_nil_inv_r {A B} (x : A) (il : inflist A) :
  ¬ inflist_same_length (x :: il) (@infnil B).
Proof. intros Heq; specialize (Heq 0) as [_ Heq]; specialize (Heq eq_refl); done. Qed.

Lemma inflist_same_length_cons {A B} (x : A) (il : inflist A) (y : B) (il' : inflist B) :
  inflist_same_length (x :: il) (y :: il') ↔ inflist_same_length il il'.
Proof.
  split.
  - by intros Heq n; specialize (Heq (S n)).
  - by intros Heq []; simpl; last apply Heq.
Qed.

Lemma inflist_same_length_drop n {A B} (il : inflist A) (il' : inflist B):
  inflist_same_length il il' → inflist_same_length (inflist_drop n il) (inflist_drop n il').
Proof. rewrite /inflist_same_length; intros Hsl k; rewrite -!inflist_drop_add; auto. Qed.

Global Hint Extern 0 =>
match goal with
| H : inflist_same_length []%inflist (_ :: _)%inflist |- _ =>
  apply inflist_same_length_nil_inv_l in H; contradiction
| H : inflist_same_length (_ :: _)%inflist []%inflist |- _ =>
  let Hf := fresh "H" in
  apply inflist_same_length_nil_inv_r in H; contradiction
end : core.

Global Instance ilist_fmap : FMap inflist :=
  λ A B f, cofix go (il : inflist A) :=
    match il with
    | [] => []
    | x :: il' => f x :: go il'
    end%inflist.

Section inflist_fmap.
  Context {A B} (f : A → B).

  Lemma inflist_fmap_length (il : inflist A) : inflist_same_length il (f <$> il).
  Proof.
    intros n; revert il; induction n; intros il.
    - rewrite (inflist_unfold_fold (f <$> il)).
      destruct il; done.
    - destruct il; simpl; done.
  Qed.

  Lemma inflist_fmap_cons_inv (il : inflist A) (b : B) (il' : inflist B) :
    f <$> il = (b :: il')%inflist → ∃ a il'', il = (a :: il'')%inflist ∧ b = f a ∧ il' = f <$> il''.
  Proof.
    rewrite (inflist_unfold_fold (f <$> il)).
    destruct il; simpl; first done.
    intros ?; simplify_eq; eauto.
  Qed.

End inflist_fmap.

Lemma inflist_take_of_same_length k {A B} (il : inflist A) (il' : inflist B) :
  inflist_same_length il il' →
  length (inflist_take k il) = length (inflist_take k il').
Proof.
  revert il il'.
  induction k as [|k IHk]; simpl; first done.
  intros il il' Hsl.
  destruct il as [|a il]; destruct il' as [|a' il'];
    [done|by apply inflist_same_length_nil_inv_l in Hsl|
       by apply inflist_same_length_nil_inv_r in Hsl|].
  rewrite /= (IHk il il'); last done.
  rewrite -> inflist_same_length_cons in Hsl; done.
Qed.
