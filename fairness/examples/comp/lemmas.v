Require Import ClassicalFacts.
Require Import stdpp.decidable.
From iris.proofmode Require Import tactics.
Require Import stdpp.decidable.
Import derived_laws_later.bi.


(* copied from coq-hahn *)
Tactic Notation "forward" tactic1(tac) :=
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1; [tac|].

Tactic Notation "forward" tactic1(tac) "as" simple_intropattern(H) :=
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1; [tac|intros H].

Tactic Notation "specialize_full" ident(H) :=
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1; [eapply H|try clear H; intro H].


(* to avoid referring to classical logic*)
Lemma min_prop_dec (P: nat -> Prop) (DEC: forall n, Decision (P n)):
  ClassicalFacts.Minimization_Property P.
Proof using. 
  red. intros n Pn.

  assert (forall p, p <= n + 1 -> ((∃ m, Minimal P m) \/ forall k, k < p -> ¬ P k)) as MIN'.
  2: { destruct (MIN' (n + 1)); eauto. edestruct H; eauto. lia. }

  induction p.
  { intros. right. lia. }
  intros. destruct IHp; [lia| auto| ].
  rewrite Nat.add_1_r in H. apply le_S_n in H. 
  destruct (DEC p).
  - left. exists p. split; auto. intros.
    destruct (decide (p <= k)); auto.
    destruct (H0 k); auto. lia.
  - right. intros. destruct (decide (k = p)); [congruence| ].
    apply H0. lia.
Qed.


Instance Minimal_proper: 
  Proper (pointwise_relation nat iff ==> eq ==> iff) ClassicalFacts.Minimal.
Proof using.
  red. red. intros. red. intros. subst. red in H. 
  split; intros [P MIN].
  all: split; [| intros; apply MIN]; apply H; auto.
Qed. 

(* useful for rewriting in equivalences *)
Lemma is_Some_Some_True {A: Type} (a: A):
  is_Some (Some a) <-> True.
Proof. done. Qed. 

(* TODO: move*)
(* useful for rewriting in equivalences *)
Lemma is_Some_None_False {A: Type}:
  is_Some (None: option A) <-> False.
Proof.
  split; [| done]. by intros []. 
Qed. 

