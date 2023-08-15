Require Import ClassicalFacts.
Require Import stdpp.decidable.
From iris.proofmode Require Import tactics.
Require Import stdpp.decidable.
Import derived_laws_later.bi.

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
