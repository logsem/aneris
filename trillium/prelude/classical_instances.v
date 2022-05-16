From trillium.prelude Require Import classical.
From stdpp Require Import prelude.

Lemma make_proof_irrel (P : Prop) : ProofIrrel P.
Proof. intros ??; apply ProofIrrelevance. Qed.

Lemma make_decision P : Decision P.
Proof.
  assert (∃ x : Decision P, True) as Hdecex.
  { destruct (ExcludedMiddle P) as [HP|HnP].
    - exists (left HP); done.
    - exists (right HnP); done. }
  apply epsilon in Hdecex; done.
Qed.
