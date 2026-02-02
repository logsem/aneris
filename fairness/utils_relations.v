Require Import Relation_Operators Operators_Properties.
From stdpp Require Import relations.
From iris.proofmode Require Import tactics.


Section RelationsUtils.
  Context {A: Type}.

  Definition rel_compose (R1 R2 : relation A): relation A :=
    fun x y => exists z, R1 x z /\ R2 z y.
  
  Global Instance rel_subseteq: SubsetEq (relation A) :=
    fun R1 R2 => forall x y, R1 x y -> R2 x y. 

  Global Instance rel_compose_mono:
    Proper (subseteq ==> subseteq ==> subseteq) rel_compose.
  Proof.
    red. intros ??????. rewrite /rel_compose.
    red. intros ?? (?&?&?). eexists. eauto.
  Qed.
  
  Lemma nsteps_0 (R: relation A) x y: nsteps R 0 x y <-> x = y.
  Proof.
    split.
    - intros STEP. by inversion STEP.
    - intros ->. constructor.
  Qed. 
  
  Lemma nsteps_1 (R: relation A) x y: nsteps R 1 x y <-> R x y.
  Proof.
    split.
    - intros STEP. inversion STEP; subst. inversion H1. by subst. 
    - intros. econstructor; eauto. constructor. 
  Qed. 
  
  Lemma rel_compose_nsteps_next' (r: relation A) n:
    forall x y,
      rel_compose r (relations.nsteps r n) x y <->
        relations.nsteps r (S n) x y.
  Proof using.
    intros. split.
    - intros (?&?&?). econstructor; eauto.
    - intros STEP. inversion STEP. subst. eexists. eauto.
  Qed. 

  Lemma rel_compose_assoc (R1 R2 R3: relation A) x y:
    rel_compose (rel_compose R1 R2) R3 x y <-> rel_compose R1 (rel_compose R2 R3) x y.
  Proof.
    intros. rewrite /rel_compose. set_solver.
  Qed. 

  Lemma rel_compose_nsteps_plus (r: relation A) n m:
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

  Lemma rel_compose_nsteps_next (r: relation A) n:
    forall x y,
      rel_compose (relations.nsteps r n) r x y <->
        relations.nsteps r (S n) x y.
  Proof using.
    intros. rewrite /rel_compose.
    setoid_rewrite <- (nsteps_1 r). setoid_rewrite rel_compose_nsteps_plus.
    f_equiv. lia. 
  Qed. 
  
  Global Instance rel_subseteq_po: PreOrder rel_subseteq.
  Proof.
    rewrite /rel_subseteq. split; eauto.
  Qed.

  Lemma strict_not_both (R: relation A) x y:
    strict R x y -> strict R y x -> False.
  Proof using.      
    clear. intros [??] [??]. done.
  Qed.

  Global Instance nsteps_mono n:
    Proper (subseteq ==> subseteq) (fun R => nsteps R n).
  Proof.
    red. induction n.
    { intros ????? ?%nsteps_0. by apply nsteps_0. }
    intros ????? (? & STEPS & STEP)%rel_compose_nsteps_next.
    eapply IHn in STEPS; eauto.
    eapply rel_compose_nsteps_next. eexists. split; eauto. 
  Qed.
  
  Lemma clos_refl_nsteps (R: relation A) x y
    (CR: clos_refl _ R x y):
    exists n, nsteps R n x y.
  Proof using.
    inversion CR; subst.
    - exists 1. by apply nsteps_1.
    - exists 0. by apply nsteps_0.
  Qed.                          
    
  Global Instance nsteps_impl:
    Proper ((eq ==> eq ==> impl) ==> eq ==> (eq ==> eq ==> impl)) (@relations.nsteps A).
  Proof using.
    red. intros ?????????????. subst. red in H.
    generalize dependent y2. induction y0.
    { intros ?. by rewrite !nsteps_0. }
    intros ?. rewrite -!rel_compose_nsteps_next.
    intros (?&STEPS&STEP). apply IHy0 in STEPS.
    eexists. split; eauto. eapply H; eauto.
  Qed. 

  Global Instance clos_trans_1n_proper_impl (R: relation A)
    (E: relation A)
    {REFL_E: Reflexive E}
    (PR: Proper (E ==> E ==> impl) R):
    Proper (E ==> E ==> impl) (clos_trans_1n _ R).
  Proof using.
    red. intros x1 x2 Ex y1 y2 Ey. intros TR.
    generalize dependent x2. generalize dependent y2.
    induction TR.
    + intros. econstructor. eapply PR; [..| apply H]; done.
    + intros y2 Ez x2 Ex.
      rename x into x1.
      rename y2 into z2. rename z into z1.
      rename y into y1.
      eapply PR in H; eauto.     
      specialize (IHTR _ Ez).
      specialize (IHTR _ ltac:(reflexivity)).
      eapply Relation_Operators.t1n_trans; eauto.
  Qed.

  Global Instance clos_trans_1n_proper_iff (R: relation A)
    (E: relation A)
    {SYM_E: Symmetric E}
    {REFL_E: Reflexive E}
    (PR: Proper (E ==> E ==> iff) R):
    Proper (E ==> E ==> iff) (clos_trans_1n _ R).
  Proof using.
    red.
    assert (Proper (E ==> E ==> impl) R).
    { intros ???????. symmetry in H, H0. 
      eapply PR; eauto. }
    intros x1 x2 Ex y1 y2 Ey. split; intros. 
    - eapply clos_trans_1n_proper_impl; eauto. 
    - symmetry in Ex, Ey. eapply clos_trans_1n_proper_impl; eauto.
  Qed. 

  Lemma clos_trans_tn1_t1n_iff (R : relation A) (x y : A):
    clos_trans_n1 A R x y ↔ clos_trans_1n A R x y.
  Proof using.
    by rewrite -clos_trans_t1n_iff clos_trans_tn1_iff.
  Qed.
  
End RelationsUtils.
