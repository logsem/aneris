From stdpp Require Import namespaces coPset. 
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import utils_logic.

Section CoPsetOrdering.
  
  Definition coPset_least (C: coPset) (INF: ¬ set_finite C) : positive :=
    let c := coPpick C in
    let m := min_prop_dec_impl_pos (fun p => p ∈ C) _ c (coPpick_elem_of _ INF) in
    proj1_sig m.

  Lemma coPset_least_spec (C: coPset) (INF: ¬ set_finite C):
    Minimal_pos (fun p => p ∈ C) (coPset_least C INF).
  Proof.
    rewrite /coPset_least.
    by destruct min_prop_dec_impl_pos.
  Qed.

  Lemma coPset_least_in (C: coPset) (INF: ¬ set_finite C):
    coPset_least C INF ∈ C. 
  Proof.
    apply coPset_least_spec. 
  Qed.

  Local Lemma coPset_sub1_helper (C: coPset) (INF: ¬ set_finite C) (m: positive):
    ¬ set_finite (C ∖ {[ m ]}).
  Proof.
    apply coPset_infinite_finite. apply difference_infinite.
    - by apply coPset_infinite_finite.
    - apply singleton_finite.
  Qed. 

  Fixpoint coPset_nth (C: coPset) (INF: ¬ set_finite C) (n: nat): positive :=
    let m := coPset_least C INF in
    match n with
    | 0 => m
    | S n => coPset_nth (C ∖ {[ m ]}) (coPset_sub1_helper C INF m) n
    end.

  Definition ns_nth (ns: namespace) :=
    coPset_nth (↑ns) (nclose_infinite ns). 

  Lemma coPset_nth_in C INF i:
    coPset_nth C INF i ∈ C. 
  Proof.
    remember (coPset_nth C INF i) as c. generalize dependent c. 
    generalize dependent C. induction i.
    { simpl. intros. subst. apply coPset_least_in. }
    simpl. intros.
    specialize (IHi _ _ _ Heqc).
    set_solver.
  Qed. 

  Lemma coPset_nth_disj_neq C1 C2 INF1 INF2 n1 n2
    (DISJ: C1 ## C2):
    coPset_nth C1 INF1 n1 ≠ coPset_nth C2 INF2 n2.
  Proof. 
    pose proof (coPset_nth_in _ INF1 n1).
    pose proof (coPset_nth_in _ INF2 n2) as IN2. 
    intros EQ. rewrite -EQ in IN2. set_solver.
  Qed. 

  Lemma coPset_nth_next_lt C INF i:
    (coPset_nth C INF i < coPset_nth C INF (S i))%positive.
  Proof using.
    remember (coPset_nth C INF i) as m. remember (coPset_nth C INF (S i)) as m'.
    generalize dependent C. generalize dependent m. generalize dependent m'.
    induction i.
    { simpl. intros.
      pose proof (coPset_least_spec C INF).
      assert (m' ∈ C) as IN'.
      { subst m'. eapply elem_of_weaken; [apply coPset_least_in| ]. set_solver. }
      red in H. apply proj2 in H. specialize (H m' IN').
      rewrite -Heqm in H. apply Positive_as_OT.le_lteq in H as [? | ?]; [lia| ].
      rewrite -Heqm in Heqm'.
      pose proof (coPset_least_in _ (coPset_sub1_helper C INF m)).
      set_solver. }
    intros.
    pose proof (coPset_sub1_helper C INF (coPset_least C INF)) as INF'.
    eapply IHi; eauto.
  Qed.

  Lemma coPset_nth_lt C INF i j (LT: i < j):
    (coPset_nth C INF i < coPset_nth C INF j)%positive.
  Proof.
    apply Nat.lt_exists_pred in LT as (? & -> & LE).
    apply Nat.le_sum in LE as [d ->]. 
    induction d.
    { rewrite Nat.add_0_r. apply coPset_nth_next_lt. }
    etrans; eauto.
    eapply Positive_as_OT.lt_le_trans; [apply coPset_nth_next_lt| ].
    apply Positive_as_OT.le_lteq. right. f_equal. lia.
  Qed.     

  Lemma coPset_nth_inj (C: coPset) (INF: ¬ set_finite C):
    Inj eq eq (coPset_nth C INF).
  Proof.
    red. intros i j EQ.
    destruct (Nat.lt_trichotomy i j) as [LT|[?|LT]]; auto.
    all: apply (coPset_nth_lt C INF) in LT; lia.
  Qed.

  Lemma coPset_nth_surj (C: coPset) (INF: ¬ set_finite C):
    forall p, p ∈ C -> exists n, p = coPset_nth C INF n. 
  Proof.
    intros p INp. 
    remember (coPset_least C INF) as m.
    remember (Pos.to_nat p - Pos.to_nat m) as d.
    generalize dependent m. generalize dependent C.
    pattern d. apply lt_wf_ind. clear d. intros d IH.     
    destruct (decide (d = 0)) as [-> | NZ]. 
    { simpl. intros. symmetry in Heqd. apply Nat.sub_0_le in Heqd.
      apply Pos2Nat.inj_le in Heqd.
      apply Positive_as_OT.le_lteq in Heqd as [LT | ->].
      2: { by exists 0. }
      pose proof (coPset_least_spec C INF). rewrite -Heqm in H.
      red in H. apply proj2 in H. specialize (H _ INp). 
      lia. }
    intros.
    set (m' := coPset_least (C ∖ {[ m ]}) (coPset_sub1_helper C INF m)).
    assert (m' ∈ C ∖ {[ m ]}) as IN'.
    { subst m'. apply coPset_least_in. }
    assert (Pos.to_nat p - Pos.to_nat m' < d) as LT'.
    { subst d. enough (Pos.to_nat m < Pos.to_nat m'); [lia| ].
      apply Pos2Nat.inj_lt.
      subst m m'. apply (coPset_nth_lt C INF 0 1). lia. }
    assert (p ∈ C ∖ {[m]}) as IN''.
    { apply elem_of_difference. split; auto.
      apply not_elem_of_singleton. intros ->. lia. }
    specialize (IH (Pos.to_nat p - Pos.to_nat m') LT' _ (coPset_sub1_helper C INF m) IN''
               _ ltac:(done) ltac:(done)).
    destruct IH as [n' EQ']. exists (S n'). simpl. set_solver.
  Qed.

End CoPsetOrdering.

Lemma ns_ndot_disj' (ns: namespace) (i: nat):
  ns ≠ ns .@ i.
Proof using.
  intros EQ.
  pose proof (coPpick_elem_of (↑ ns .@ (i + 1)) (nclose_infinite _)) as IN.
  pose proof IN as IN'. rewrite {2}EQ in IN'.
  apply nclose_subseteq in IN'.
  edestruct @ndot_ne_disjoint; [| apply IN | apply IN'].
  lia. 
Qed.   

(* TODO: can be proved simpler if we could unfold ndot *)
Lemma ns_ndot_diff_not_subseteq (ns: namespace) (i j: nat)
  (NEQ: i ≠ j):
  (↑ (ns .@ i): coPset) ⊈ ↑ (ns .@ j).
Proof.
  intros EQ.
  pose proof (coPpick_elem_of (↑ ns .@ i) (nclose_infinite _)) as IN1.
  edestruct @ndot_ne_disjoint; [| apply IN1 | ].
  2: { apply EQ. done. }  
  done. 
Qed. 

Lemma ns_ndot_disj (ns: namespace) (i j: nat)
  (NEQ: i ≠ j):
  ns .@ i ≠ ns .@ j.
Proof using.
  intros EQ. edestruct (ns_ndot_diff_not_subseteq ns); eauto.
  by rewrite EQ.
Qed. 
