From iris.proofmode Require Import tactics coq_tactics.
From iris.base_logic.lib Require Import invariants.


Section BoundedNat.
  Context (N: nat).

  Definition bounded_nat := { i | i < N }.
  
  Definition bounded_nat_le (x y: bounded_nat) := `x <= `y. 
 
  Global Instance nat_bounded_PO: PartialOrder bounded_nat_le. 
  Proof using.
    split.
    - split.
      + red. intros. red. reflexivity.
      + red. intros [??] [??] [??]. rewrite /bounded_nat_le. simpl. lia.
    - red. intros [??] [??]. rewrite /bounded_nat_le. simpl.
      intros. assert (x = x0) by lia. subst.
      assert (l0 = l) by apply Nat.lt_pi. congruence.
  Qed.

  Definition BNOfe := sigO (fun i => i < N).

  Definition ith_bn (i: nat) (LT: i < N): bounded_nat :=
    exist _ i LT.

  Lemma ith_bn_lt i j Bi Bj
    (LTij: i < j):
    strict bounded_nat_le (ith_bn i Bi) (ith_bn j Bj).
  Proof using.
    rewrite /ith_bn /bounded_nat_le.
    red. apply strict_spec_alt. split.
    { simpl. lia. }
    simpl. red. simpl. lia.
  Qed.

  Definition bn2nat (b: bounded_nat) := proj1_sig b. 

End BoundedNat.
