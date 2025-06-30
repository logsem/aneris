From iris.proofmode Require Import tactics coq_tactics.
From iris.base_logic.lib Require Import invariants.
From trillium.prelude Require Import finitary.

Definition unit_rel (_: unit) (_: unit) := True. 

Global Instance unit_PO: PartialOrder unit_rel.
Proof using.
  split.
  - split; done.
  - red. by intros [] [].
Qed.

Lemma unit_WF: well_founded (strict unit_rel).
Proof using.
  red. intros x. constructor.
  intros y NE. destruct x, y.
  by apply strict_ne in NE.
Qed.

Definition empty_rel (_: Empty_set) (_: Empty_set) := True.

Global Instance empty_PO: PartialOrder empty_rel.
Proof using.
  split. 
  - split; done.
  - red. done.
Qed.  

Lemma empty_WF: well_founded (strict empty_rel).
Proof using. done. Qed.


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

  Lemma fin_wf: well_founded (strict bounded_nat_le).
  Proof using.
    eapply (well_founded_lt_compat _ proj1_sig).
    intros [??] [??]. rewrite strict_spec. rewrite /bounded_nat_le.
    simpl. lia.
  Qed.     

  Lemma lvl_lt_equiv (l1 l2: bounded_nat):
    strict bounded_nat_le l1 l2 <-> bn2nat l1 < bn2nat l2.
  Proof using.
    destruct l1, l2; simpl in *.
    rewrite strict_spec_alt. simpl.
    rewrite /bounded_nat_le. simpl. split.
    - intros [? ?]. apply PeanoNat.Nat.le_neq. split; auto.
      intros ->. destruct H0. f_equal. apply Nat.lt_pi.
    - intros ?. split; [lia| ]. intros ?. inversion H0. subst. lia.
  Qed.
    
End BoundedNat.

Definition bn_ith N (i: nat): bounded_nat (S N) :=
  match (le_lt_dec (S N) i) with
  | left GE => ith_bn (S N) 0 ltac:(lia)                                      
  | right LT => ith_bn (S N) i LT
  end.

Lemma bn_ith_simpl N i (DOM: i < S N):
    bn_ith N i = ith_bn (S N) i DOM.
Proof.      
  rewrite /bn_ith. destruct le_lt_dec; [lia| ].
  f_equal. eapply Nat.lt_pi.
Qed.

