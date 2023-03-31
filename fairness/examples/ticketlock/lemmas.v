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
  set (cands := filter P (seq 0 (n + 1))).
  destruct cands eqn:C; simpl.
  { subst cands.
    pose proof (@filter_nil_not_elem_of _ _ DEC _ _ C Pn).
    destruct H. apply elem_of_seq. lia. } 
  (* exists n0. split. *)
  (* { eapply proj1. eapply elem_of_list_filter. *)
  (*   apply elem_of_list_filter.  *)
Admitted.


Instance Minimal_proper: 
  Proper (pointwise_relation nat iff ==> eq ==> iff) ClassicalFacts.Minimal.
Proof using.
  red. red. intros. red. intros. subst. red in H. 
  split; intros [P MIN].
  all: split; [| intros; apply MIN]; apply H; auto.
Qed. 

