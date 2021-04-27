From Coq.Unicode Require Import Utf8.
From stdpp Require Import base.
From aneris.prelude Require Import classical.
From Coq.ssr Require Import ssreflect.

Lemma sig_eq {A} (P : A → Prop) (x y : sig P) :
  proj1_sig x = proj1_sig y → x = y.
Proof.
  destruct x as [x Px]; simpl.
  destruct y as [y Py]; simpl.
  intros ->.
  rewrite (ProofIrrelevance _ Px Py); trivial.
Qed.

Definition sig_prod_and {A B P Q} (a : {x : A | P x}) (b : {x : B | Q x}) :
    {x : A * B | P (fst x) ∧ Q (snd x)} :=
  (proj1_sig a, proj1_sig b) ↾ (conj (proj2_sig a) (proj2_sig b)).

Definition sig_prod_or_l {A P Q} (a : {x : A | P x}) :
  {x : A | P x ∨ Q x} := (proj1_sig a) ↾ (or_introl (proj2_sig a)).

Definition sig_prod_or_r {A P Q} (a : {x : A | Q x}) :
    {x : A | P x ∨ Q x} := (proj1_sig a) ↾ (or_intror (proj2_sig a)).

Instance sig_or_eq_dec {A P Q} `{!EqDecision A} :
  EqDecision {x : A | P x ∨ Q x}.
Proof.
  intros [a1 Ha1] [a2 Ha2]; simpl in *.
  destruct (decide (a1 = a2)) as [->|]; last first.
  { right; inversion 1; done. }
  left.
  apply sig_eq; done.
Qed.
