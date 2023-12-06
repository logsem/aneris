From trillium.fairness Require Import inftraces trace_len subtrace my_omega lemmas.

Local Ltac gd t := generalize dependent t.

Definition traces_equiv {St L: Type} :=
  @traces_match L L St St eq eq (fun _ _ _ => True) (fun _ _ _ => True).

Axiom traces_equiv_eq:
  forall {St L: Type} (t1 t2: trace St L), traces_equiv t1 t2 -> t1 = t2. 

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
  intros ?? ->%traces_equiv_eq ?? ->%traces_equiv_eq. done.
Qed. 

Instance upto_stutter_Proper {St S' L L': Type} {Us: St -> S'} {Usls: St -> L -> St -> option L'}:
  Proper (@traces_equiv St L ==> @traces_equiv S' L' ==> iff)
    (upto_stutter Us Usls).
Proof. 
  red. intros ??????. split.
  - intros. eapply upto_stutter_Proper_impl; eauto.
  - intros. apply traces_equiv_symm in H, H0. 
    eapply upto_stutter_Proper_impl; eauto.
Qed.
