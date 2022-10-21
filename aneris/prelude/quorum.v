Require Import Arith ZArith ZArith ZifyClasses ZifyInst Lia.
From Coq.ssr Require Import ssreflect.
From stdpp Require Import base gmap fin_sets.

(* For the [lia] tactic to support [Nat.div]. *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.
#[global] Program Instance Op_Nat_div : BinOp Nat.div :=
  {| TBOp := Z.div ; TBOpInj := Nat2Z.inj_div |}.
Add Zify BinOp Op_Nat_div.

Record Quorum `{Countable A} (X : gset A) := quorum {
  quorum_car :> gset A → Prop;
  quorum_subseteq Q : quorum_car Q → Q ⊆ X;
  quorum_intersection_nonempty Q1 Q2 :
    quorum_car Q1 → quorum_car Q2 → Q1 ∩ Q2 ≠ ∅;
}.
Arguments quorum {_ _ _}.
Arguments quorum_car : simpl never.
Arguments quorum_subseteq {_ _ _ _}.
Arguments quorum_intersection_nonempty {_ _ _ _}.

Lemma quorum_choose `{Countable A, QuorumX : Quorum X} (Q1 Q2 : gset A) :
  QuorumX Q1 → QuorumX Q2 → ∃ a, a ∈ Q1 ∩ Q2.
Proof.
  intros ??. by eapply set_choose_L, quorum_intersection_nonempty.
Qed.

Program Definition Quorum_majority `{Countable A} (X : gset A) : Quorum X :=
  quorum _ (λ Q, size X / 2 < size Q ∧ Q ⊆ X) _ _.
Next Obligation. by destruct 1. Qed.
Next Obligation.
  intros ?????? [? ?] [? ?] ?.
  assert (size Q1 + size Q2 ≤ size X).
  { rewrite -size_union; [set_solver|].
    by apply subseteq_size, union_subseteq. }
  lia.
Qed.
