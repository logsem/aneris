From trillium.fairness Require Import inftraces trace_len subtrace my_omega lemmas.

Local Ltac gd t := generalize dependent t.

Definition traces_equiv {St L: Type} :=
  @traces_match L L St St eq eq (fun _ _ _ => True) (fun _ _ _ => True).

(* Lemma after_equiv {St L: Type} (tr1 tr *)
(* Lemma subtrace _inf_after_equiva *)
Lemma trace_prefix_inf_equiv_id {St L: Type} (tr: trace St L) ml len
  (LEN: trace_len_is tr len)
  (LE: NOmega.le len ml):
  traces_equiv tr (trace_prefix_inf tr ml).
Proof.
  gd tr. gd ml. gd len. 
  cofix CIH.
  intros. 
  rewrite trace_prefix_inf_step_equiv.
  rewrite (trace_unfold_fold tr).
  destruct tr.
  { rewrite /trace_prefix_inf_step_alt. simpl.
    destruct decide; by econstructor. }
  rewrite /trace_prefix_inf_step_alt. simpl.
  eapply trace_len_tail in LEN.
  rewrite decide_False.
  2: { lia_NO' ml; lia_NO' len.
       destruct (decide (2 <= n0)).
       { lia. }
       replace (Nat.pred n0) with 0 in LEN; [| lia].
       by eapply trace_len_0_inv in LEN. }
  econstructor; try done.
  specialize_full CIH; [| by apply LEN| by apply CIH]. 
  lia_NO' ml; lia_NO' len. 
Qed.


Lemma subtrace_equiv_after {St L: Type} (tr str: trace St L) i ml len
  (LEN: trace_len_is tr len)
  (LE: NOmega.le len ml)
  (SUB: subtrace tr i ml = Some str)
  (* (DOM: NOmega.lt_nat_l start fin *)
  :
  exists atr, after i tr = Some atr /\
  traces_equiv atr str.
Proof.
  rewrite /subtrace in SUB.
  destruct after eqn:AFTER; [| done]. destruct decide; [done| ].
  eexists. split; eauto.  
  inversion SUB. subst str.
  eapply trace_prefix_inf_equiv_id. 
  - eapply trace_len_after; eauto.
  - lia_NO' ml; lia_NO' len.
Qed.


Instance traces_equiv_refl {St L: Type}:
  Reflexive (@traces_equiv St L). 
Proof.
  red. cofix CIH.
  intros tr. rewrite (trace_unfold_fold tr).  
  destruct tr.
  - constructor. done. Guarded.  
  - constructor; try done.
    by apply CIH. 
Qed. 


Global Instance traces_equiv_symm {St L: Type}:
  Symmetric (@traces_equiv St L). 
Proof.
  red. 
  cofix CIH.
  intros tr1 tr2 EQ. 
  rewrite (trace_unfold_fold tr1) (trace_unfold_fold tr2).
  destruct tr1, tr2.
  - constructor. inversion EQ. done. 
  - by inversion EQ. 
  - by inversion EQ. 
  - inversion EQ. subst.
    constructor; try done.
    by apply CIH. 
Qed. 


From Paco Require Import paco1 paco2 pacotac.
Lemma upto_stutter_Proper_impl {St S' L L': Type} {Us: St -> S'} {Usls: St -> L -> St -> option L'}:
  Proper (@traces_equiv St L ==> @traces_equiv S' L' ==> impl)
    (upto_stutter Us Usls).
Proof. 
  red. intros t1 t1' EQ1 t2 t2' EQ2 UPTO.
  gd t1. gd t2. gd t1'. gd t2'.
  (* pcofix CIH.  *)
  pcofix CIH. 
  pfold.

  intros. 
  erewrite (trace_unfold_fold t1'), (trace_unfold_fold t2') in *. 
  erewrite (trace_unfold_fold t1), (trace_unfold_fold t2) in *. 
  (* pfold. punfold UPTO; [| admit]. *) 
  punfold UPTO; [| apply upto_stutter_mono].
  inversion UPTO; subst.
  - destruct t1, t2; try done.
    inversion EQ1; inversion EQ2; subst; try done.    
    inversion H0. inversion H. subst.
    destruct t1', t2'; try done.
    inversion H2. inversion H5. subst.
    econstructor.
  - destruct t1, t2, t1', t2'; try by done.
    all: inversion EQ1; inversion EQ2; subst; try by done.
    + inversion H. simpl in H2. subst.
      Guarded. 
      specialize (CIH ⟨ Us s2 ⟩ t1' ⟨ Us s2 ⟩).
      specialize CIH with (t1 := t1).
      Guarded.
      specialize_full CIH.
      4: { rewrite /upaco2.
           (* eapply upto_stutter_stutter. *)
           (* 4: { eapply upto_stutter_stutter.  *)
           (* 2: { econstructor.  *)
           (* (* 2: { ??? *) *)
           (* all: admit. } *)
Admitted. 

Instance upto_stutter_Proper {St S' L L': Type} {Us: St -> S'} {Usls: St -> L -> St -> option L'}:
  Proper (@traces_equiv St L ==> @traces_equiv S' L' ==> iff)
    (upto_stutter Us Usls).
Proof. 
  red. intros ??????. split.
  - intros. eapply upto_stutter_Proper_impl; eauto.
  - intros. apply traces_equiv_symm in H, H0. 
    eapply upto_stutter_Proper_impl; eauto.
Qed.
