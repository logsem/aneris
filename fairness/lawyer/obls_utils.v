From stdpp Require Import relations.
From iris.proofmode Require Import tactics.

(* TODO: find existing definition *)
Definition rel_compose {A: Type} (R1 R2 : relation A): relation A :=
  fun x y => exists z, R1 x z /\ R2 z y.

(* TODO: find existing *)
Global Instance rel_subseteq {A: Type}: SubsetEq (relation A) :=
  fun R1 R2 => forall x y, R1 x y -> R2 x y. 

Global Instance rel_compose_mono {A: Type}:
  Proper (subseteq ==> subseteq ==> subseteq) (@rel_compose A).
Proof.
  red. intros ??????. rewrite /rel_compose.
  red. intros ?? (?&?&?). eexists. eauto.
Qed.

Lemma nsteps_0 {A} (R: relation A) x y: nsteps R 0 x y <-> x = y.
Proof.
  split.
  - intros STEP. by inversion STEP.
  - intros ->. constructor.
Qed. 

Lemma nsteps_1 {A} (R: relation A) x y: nsteps R 1 x y <-> R x y.
Proof.
  split.
  - intros STEP. inversion STEP; subst. inversion H1. by subst. 
  - intros. econstructor; eauto. constructor. 
Qed. 

Lemma rel_compose_nsteps_next' {A: Type} (r: relation A) n:
  forall x y,
    rel_compose r (relations.nsteps r n) x y <->
      relations.nsteps r (S n) x y.
Proof using.
  intros. split.
  - intros (?&?&?). econstructor; eauto.
  - intros STEP. inversion STEP. subst. eexists. eauto.
Qed. 

Lemma rel_compose_assoc {A: Type} (R1 R2 R3: relation A):
  forall x y,
    rel_compose (rel_compose R1 R2) R3 x y <-> rel_compose R1 (rel_compose R2 R3) x y.
Proof.
  intros. rewrite /rel_compose. set_solver.
Qed. 

Lemma rel_compose_nsteps_plus {A: Type} (r: relation A) n m:
  forall x y,
    rel_compose (relations.nsteps r n) (relations.nsteps r m) x y <->
      relations.nsteps r (n + m) x y.
Proof using.
  intros. generalize dependent y. generalize dependent x. induction n; intros.
  { rewrite /rel_compose. simpl. setoid_rewrite nsteps_0. set_solver. }    
  rewrite Nat.add_succ_l -rel_compose_nsteps_next'. 
  rewrite /rel_compose. setoid_rewrite <- rel_compose_nsteps_next'.
  setoid_rewrite rel_compose_assoc. rewrite /rel_compose.
  by setoid_rewrite IHn. 
Qed. 

Lemma rel_compose_nsteps_next {A: Type} (r: relation A) n:
  forall x y,
    rel_compose (relations.nsteps r n) r x y <->
      relations.nsteps r (S n) x y.
Proof using.
  intros. rewrite /rel_compose.
  setoid_rewrite <- (nsteps_1 r). setoid_rewrite rel_compose_nsteps_plus.
  f_equiv. lia. 
Qed. 

Global Instance rel_subseteq_po {A: Type}: PreOrder (@rel_subseteq A).
Proof.
  rewrite /rel_subseteq. split; eauto.
Qed.
