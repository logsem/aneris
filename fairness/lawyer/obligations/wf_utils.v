Require Import Coq.Program.Wf.
From stdpp Require Import relations.


Section WfSetMin.
  Context {A: Type}.

  Definition minimal_in_prop (R : relation A) (x : A) (P : A -> Prop) :=
    forall y, P y -> R y x -> R x y. 
  
  Context {R: relation A}.
  Hypothesis (WF: wf R).

  Theorem sets_have_min (P: A -> Prop)
    (NE: exists a, P a):
    exists a, P a /\ minimal_in_prop R a P.
  Proof. Admitted.
  
End WfSetMin.
