From iris.proofmode Require Import tactics coq_tactics.
From iris.base_logic.lib Require Import invariants.
From trillium.prelude Require Import finitary.


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

  Global Instance lvl2nat_inj: Inj eq eq bn2nat.
  Proof using.
    intros [??] [??]. simpl. intros ->.
    f_equal. apply Nat.lt_pi.
  Qed.
    
  Global Instance sig_lt_LE: 
    LeibnizEquiv (sigO (λ i, i < N)).
  Proof using.
    red. intros [??] [??]. simpl.
    rewrite sig_equiv_def. simpl.
    rewrite leibniz_equiv_iff. intros ->.
    f_equal. apply Nat.lt_pi.
  Qed. 

  Global Instance fin_ofe_lt: finite.Finite BNOfe.
  Proof using.
    unshelve eapply (@finite.surjective_finite {i | i < N}).
    { exact id. }
    2: by apply _.
    eapply (finitary.in_list_finite (seq 0 N)).
    intros. apply elem_of_seq. lia.
  Qed.  

  Lemma fin_wf: wf (strict bounded_nat_le).
  Proof using.
    eapply (well_founded_lt_compat _ proj1_sig).
    intros [??] [??]. rewrite strict_spec. rewrite /bounded_nat_le.
    simpl. lia.
  Qed.     

End BoundedNat.
