Require Import Coq.Program.Wf.
From stdpp Require Import relations.
Require Import Coq.Logic.ClassicalChoice.


Section WfSetMin.
  Context {A: Type}.

  Definition minimal_in_prop (R : relation A) (x : A) (P : A -> Prop) :=
    forall y, P y -> R y x -> False. 
  
  Context {R: relation A}.
  Hypothesis (WF: wf R).

  Theorem sets_have_min (P: A -> Prop)
    (NE: exists a, P a):
    exists a, P a /\ minimal_in_prop R a P.
  Proof.
    destruct NE as [a Pa].
    induction a as [a IH] using (well_founded_induction WF). 
    destruct (classic (exists b, P b /\ R b a)) as [(?&?&?) | MIN].
    { eapply IH; eauto. }
    exists a. split; eauto.
    red. intros b Pb Rba. apply MIN. eauto.
  Qed.
  
End WfSetMin.
