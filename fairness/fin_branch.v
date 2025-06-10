From stdpp Require Import base sets.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import utils.


Section ListApprox.
  Context {A: Type}.

  Definition list_approx (P: A -> Prop) :=
    { l: list A | forall a, P a -> a ∈ l }. 

  Fixpoint list_approx_repeat (R: A -> A → Prop)
      (APX: forall a, list_approx (R a))      
      (n: nat)
      (a: A)
      :=
      match n with
      | 0 => [a]
      | S n =>
          let la := APX a in
          flat_map (list_approx_repeat R APX n) (proj1_sig la)
      end.

  Lemma list_approx_repeat_spec (R: A -> A -> Prop) APX n a:
    forall b, relations.nsteps R n a b -> b ∈ list_approx_repeat R APX n a.
  Proof using.
    revert a. induction n.
    { simpl. intros ??. rewrite nsteps_0. set_solver. }
    intros ??. rewrite -rel_compose_nsteps_next'.       
    intros (? & STEP & STEPS). 
    apply IHn in STEPS. simpl.
    apply elem_of_list_In. apply in_flat_map. eexists. split.
    2: eapply elem_of_list_In; eauto.
    destruct APX. simpl in *. apply elem_of_list_In. eauto.
  Qed.

End ListApprox.

Section SmallerCardLA.
  Context {A: Type}.
  Context {EQDEC: EqDecision A}.
  Context (P: A -> Prop).

  From trillium.prelude Require Import classical_instances.
  
  Local Instance P_PI: forall a, ProofIrrel (P a).
  Proof using. intros. apply make_proof_irrel. Qed.  

  Lemma list_approx_smaller_card (APX: list_approx P):
    quantifiers.smaller_card {a | P a} nat.
  Proof using EQDEC.
    apply finitary.finite_smaller_card_nat.
    destruct APX as [??]. 
    by eapply finitary.in_list_finite.
  Qed.

End SmallerCardLA.


