From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
Require Import stdpp.decidable.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness.heap_lang Require Import simulation_adequacy_lm.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From stdpp Require Import finite.
From trillium.fairness Require Import fairness_finiteness actual_resources_interface. 

Import derived_laws_later.bi.

From trillium.fairness Require Import lm_fairness_preservation fuel_ext lm_fair.
From trillium.fairness.examples.comp Require Import comp.
From trillium.fairness Require Import fair_termination_natural.
From trillium.fairness.examples.comp Require Import my_omega lemmas trace_len trace_helpers subtrace trace_lookup.

From trillium.fairness Require Import lm_fairness_preservation_wip.

Close Scope Z_scope. 

Local Ltac gd t := generalize dependent t.

Instance client_trans'_PI s x: 
  ProofIrrel ((let '(s', ℓ) := x in 
               fmtrans client_model_impl s ℓ s' \/ (s' = s /\ ℓ = None)): Prop).
Proof. apply make_proof_irrel. Qed.    

Local Instance step'_eqdec: forall s1, EqDecision
                  {'(s2, ℓ) : client_model_impl *
                              option (fmrole client_model_impl) | 
                  fmtrans client_model_impl s1 ℓ s2 ∨ 
                  s2 = s1 ∧ ℓ = None}.
  (* TODO: why it stopped being inferred automatically? *)
  pose proof (fmstate_eqdec client_model_impl).
  solve_decision. 
Qed.
  
Lemma client_model_finitary (s1 : fmstate client_model_impl):
    Finite
      {'(s2, ℓ) : client_model_impl * option (fmrole client_model_impl) | 
      fmtrans client_model_impl s1 ℓ s2 ∨ s2 = s1 ∧ ℓ = None}. 
Proof. Admitted. 


Section ClientRA.

  Definition clientPreΣ : gFunctors :=
    #[ GFunctor (authUR (optionR (exclR natO)));
       fairnessΣ lib_grole lib_model_impl].
  
  Global Instance subG_clientPreΣ {Σ}:
    subG clientPreΣ Σ → clientPreGS Σ.
  Proof. solve_inG. Qed.

End ClientRA.


Lemma δ_lib0_init_roles:
  live_roles lib_model_impl 1 ⊆ dom ({[ρlg := 5]}: gmap lib_grole nat).
Proof. 
  (* TODO: definition hidden under Opaque *)
Admitted. 

Definition δ_lib0: LiveState lib_grole lib_model_impl.
  refine (build_LS_ext 1 {[ ρlg := 5 ]} _ {[ ρlg := {[ ρl ]} ]} _ _ (LM := lib_model)).
  - apply δ_lib0_init_roles.  
  - intros.
    rewrite dom_singleton. setoid_rewrite lookup_singleton_Some.
    split; intros.
    + exists ρ, {[ ρl ]}. set_solver.
    + destruct H as (?&?&?&?). by destruct ρ.
  - intros. 
    erewrite lookup_singleton_Some in H.
    rewrite lookup_singleton_Some in H0.
    destruct H, H0. congruence.
Defined. 

  


(* Definition is_client_step (step: client_state * option (option client_role * client_state)) := *)
(*   exists st1 st2, step = (st1, Some (Some $ inr ρy, st2)).  *)

(* Definition is_lib_step (step: client_state * option (option client_role * client_state)) := *)
(*   exists st1 ρlg st2, step = (st1, Some (Some $ inl ρlg, st2)).  *)

Definition step_label_matches (step: client_state * option (option client_role * client_state)) (P: client_role -> Prop) :=
  exists st1 ρ st2, step = (st1, Some (Some $ ρ, st2)) /\ P ρ.
  
  
Instance slm_dec P (DECP: forall ρ, Decision (P ρ)):
  forall step, Decision (step_label_matches step P).
Proof. 
  rewrite /step_label_matches. intros [? p2].
  destruct p2 as [p2| ]. 
  2: { right. intros (?&?&?&?). intuition. congruence. }
  destruct p2 as [or s2].
  destruct or as [r |]. 
  2: { right. intros (?&?&?&?). intuition. congruence. }
  destruct (decide (P r)).
  - left. subst. do 2 eexists. eauto.
  - right. intros (?&?&?&?). intuition. congruence. 
Qed. 


Definition is_client_step := fun step => step_label_matches step (eq (inr ρy)).     
Definition is_lib_step := fun step => step_label_matches step 
                                     (fun ρ => exists ρlg, inl ρlg = ρ).     

Lemma client_steps_finite (tr: mtrace client_model_impl)
  (VALID: mtrace_valid tr)
  (CL: ∀ i s step, tr !! i = Some (s, step) → is_client_step (s, step) \/ step = None):
  exists l, trace_len_is tr (NOnum l) /\ 
         (forall s, tr S!! (l - 1) = Some s -> snd s = snd (trfirst tr) - (l - 1)). 
Proof.
  pose proof (state_lookup_0 tr) as S0.
  destruct (trfirst tr) as [δ0 c0] eqn:ST0. 
  gd tr. gd δ0. induction c0.
  { intros. exists 1.
    pose proof (trace_has_len tr) as [len LEN].
    destruct (tr !! 0) as [[δ0_ c0_]| ] eqn:STEP0.
    2: { eapply trace_lookup_dom_neg in STEP0; eauto.
         lia_NO' len. assert (n = 0) as -> by lia. 
         by apply trace_len_0_inv in LEN. }
    forward eapply trace_state_lookup_simpl; eauto. intros ->.
    specialize (CL _ _ _ STEP0). destruct CL.
    2: { subst. 
         pattern (δ0, 0) in STEP0. eapply ex_intro, trace_lookup_dom_eq in STEP0; eauto. subst.
         simpl in *. split; auto.
         intros. destruct s. simpl in *. congruence. }
    do 2 red in H. destruct H as (?&?&?&[[=] <-]). subst.
    pose proof (mtrace_valid_steps' VALID _ _ _ _ STEP0) as STEP.
    inversion STEP. }

  intros.
  pose proof (trace_has_len tr) as [len LEN].
  destruct (tr !! 0) as [[δ0_ c0_]| ] eqn:STEP0.
  2: { eapply trace_lookup_dom_neg in STEP0; eauto.
       lia_NO' len. assert (n = 0) as -> by lia. 
       by apply trace_len_0_inv in LEN. }
  forward eapply trace_state_lookup_simpl; eauto. intros ->.

  pose proof CL as CL'. specialize (CL' _ _ _ STEP0).
  destruct CL'.
  2: { subst. 
       pattern (δ0, S c0) in STEP0. eapply ex_intro, trace_lookup_dom_eq in STEP0; eauto. subst.
       simpl in *. eexists. split; eauto.
       intros. destruct s. simpl in *. congruence. }
  do 2 red in H. destruct H as (?&?&?&[[=] <-]). subst.
  pose proof (mtrace_valid_steps' VALID _ _ _ _ STEP0) as STEP.
  destruct x1 as [δ1 c0_].
  assert (c0_ = c0) as ->. 
  { inversion STEP; lia. }
  pose proof STEP0 as (atr & AFTER & HEAD)%trace_lookup_after_strong.
  apply after_S_tr_cons in AFTER. 
  specialize (IHc0 δ1 atr). specialize_full IHc0; eauto. 
  { eapply mtrace_valid_after; eauto. }
  { intros. apply (CL (S i)). rewrite -H.
    symmetry. rewrite -Nat.add_1_r Nat.add_comm.
    eapply trace_lookup_after; eauto. }
  { by rewrite -HEAD -state_lookup_0. }
  destruct IHc0 as (l' & LEN' & C).
  destruct l'.
  { simpl in LEN'. by apply trace_len_0_inv in LEN'. }
  exists (S l' + 1). split.
  { forward eapply (trace_len_after tr) as LEN'_; eauto.
    forward eapply (trace_len_uniq _ _ _ LEN' LEN'_) as L_; eauto.
    lia_NO' len. inversion L_. subst.
    enough (S (l' + 1) = n); [subst; done| ]. lia. } 
  intros. destruct s as [δ c].
  erewrite state_lookup_after in C; eauto.
  simpl. simpl in C. rewrite Nat.sub_0_r.
  rewrite Nat.add_sub in H. rewrite Nat.sub_0_r in C. 
  specialize (C _ H). simpl in *. lia. 
Qed. 

(* Lemma client_steps_finite (tr: mtrace client_model_impl) *)
(*   (VALID: mtrace_valid tr) *)
(*   (CL: ∀ i s step, tr !! i = Some (s, step) → is_client_step (s, step) \/ step = None): *)
(*   (* exists l, trace_len_is tr (NOnum l) /\ (l = 0 /\ snd (trfirst tr) =  *) *)
(*   terminating_trace tr.  *)
(* Proof. *)
(*   pose proof (trace_has_len tr) as [len LEN].  *)
(*   lia_NO' len. *)
(*   2: { eapply terminating_trace_equiv; eauto. } *)
(*   exfalso. *)
(*   assert (exists s0, tr S!! 0 = Some s0) as [[δ0 c0] S0]. *)
(*   { pose proof (inf_trace_lookup _ LEN 0) as ([δ0 c0] & ℓ0 & s1 & L0). *)
(*     apply state_label_lookup in L0 as (?&?&?). eauto. }  *)
(*   gd tr. gd δ0. induction c0. *)
(*   { intros. *)
(*     pose proof (inf_trace_lookup _ LEN 0) as (? & ℓ & ? & L0). *)
(*     forward eapply trace_state_lookup_simpl as EQ; eauto. subst x.   *)
(*     pose proof (mtrace_valid_steps' VALID _ _ _ _ L0) as S. by inversion S. } *)
(*   intros. destruct tr. *)
(*   { specialize (LEN 1). simpl in *. *)
(*     by pose proof (proj2 LEN I) as []. } *)
(*   pose proof (inf_trace_lookup _ LEN 0) as (? & ? & [δ1 c1] & L0). *)
(*   forward eapply trace_state_lookup_simpl as EQ; eauto. subst x.   *)
(*   pose proof (mtrace_valid_steps' VALID _ _ _ _ L0). *)
  
(*   assert (c1 = c0) as ->. *)
(*   { specialize (CL _ _ _ L0). destruct CL as [CL|?]; [| done]. *)
(*     do 2 red in CL. destruct CL as (?&?&?&[? <-]). *)
(*     inversion H0. subst. clear H0.  *)
(*     inversion H; lia. } *)
  
(*   assert (tr S!! 0 = Some (δ1, c0)) as L1. *)
(*   { apply state_label_lookup in L0 as (_&?&_). *)
(*     rewrite Nat.add_1_r in H0. by rewrite state_lookup_cons in H0. } *)

(*   apply trace_len_tail in LEN. *)
(*   eapply (IHc0 δ1 tr); eauto.   *)
(*   { eapply mtrace_valid_tail; eauto. } *)
(*   intros. left. *)
(*   pose proof (CL (S i) _ _ H0) as [? | ->]; [done| ]. *)
(*   pattern s0 in H0. eapply ex_intro, trace_lookup_dom_eq in H0; eauto. *)
(*   done.  *)
(* Qed.  *)

(* Lemma client_steps_finite (tr: mtrace client_model_impl) (l len: nat_omega) *)
(*   (VALID: mtrace_valid tr) *)
(*   (LEN: trace_len_is tr len) *)
(*   (LE: NOmega.le l len) *)
(*   (CL: ∀ i res, NOmega.lt (NOnum i) l → tr !! i = Some res → is_client_step res): *)
(*   exists m, l = NOnum m. *)
(* Proof. *)
(*   lia_NO' l; lia_NO' len; try by eauto. exfalso. *)
(*   assert (exists s0, tr S!! 0 = Some s0) as [[δ0 c0] S0]. *)
(*   { pose proof (inf_trace_lookup _ LEN 0) as ([δ0 c0] & ℓ0 & s1 & L0). *)
(*     apply state_label_lookup in L0 as (?&?&?). eauto. }  *)
(*   gd tr. gd δ0. clear LE. induction c0. *)
(*   { intros. *)
(*     pose proof (inf_trace_lookup _ LEN 0) as (? & ℓ & ? & L0). *)
(*     forward eapply trace_state_lookup_simpl as EQ; eauto. subst x.   *)
(*     pose proof (mtrace_valid_steps' VALID _ _ _ _ L0) as S. by inversion S. } *)
(*   intros. destruct tr. *)
(*   { specialize (LEN 1). simpl in *. *)
(*     by pose proof (proj2 LEN I) as []. } *)
(*   pose proof (inf_trace_lookup _ LEN 0) as (? & ? & [δ1 c1] & L0). *)
(*   forward eapply trace_state_lookup_simpl as EQ; eauto. subst x.   *)
(*   pose proof (mtrace_valid_steps' VALID _ _ _ _ L0). *)
(*   assert (c1 = c0) as ->. *)
(*   { specialize (CL _ _ I L0). do 2 red in CL. destruct CL as (?&?&?&[? <-]). *)
(*     inversion H0. subst. clear H0.  *)
(*     inversion H; lia. } *)
  
(*   assert (tr S!! 0 = Some (δ1, c0)) as L1. *)
(*   { apply state_label_lookup in L0 as (_&?&_). *)
(*     rewrite Nat.add_1_r in H0. by rewrite state_lookup_cons in H0. } *)

(*   eapply (IHc0 δ1 tr); eauto.   *)
(*   { eapply mtrace_valid_tail; eauto. } *)
(*   { by apply trace_len_tail in LEN. } *)
(*   intros. apply (CL (S i)); [done| ]. *)
(*   rewrite trace_lookup_cons; eauto.  *)
(* Qed.  *)

Arguments NOmega.le _ _ : simpl nomatch.


(* Definition is_lib_step_alt (step: client_state * option (option client_role * client_state)): Prop. *)
(*   := snd step *)

(* TODO: unify with other decision lemmas about client model *)
Instance client_trans_dec: forall c1 oρ c2, 
    Decision (client_trans c1 oρ c2).
Proof. Admitted. 
  


CoFixpoint project_lib_trace (tr: mtrace client_model_impl):
  auxtrace (LM := lib_model). 
destruct tr.
{ exact ⟨ fst s ⟩. }
(* cases not corresponding to library role
   should be ruled out during actual construction *)
destruct ℓ.
2: { exact ⟨ fst s ⟩. }
destruct f.
2: { exact ⟨ fst s ⟩. }
set (fls := allowed_step_FLs (fst s) f (fst $ trfirst tr) (LM := lib_model)).
destruct (decide (fls = ∅)).
{ exact ⟨ fst s ⟩. }
assert (elements fls ≠ []).
{ intros ?%elements_empty_inv. set_solver. }
destruct (elements fls) eqn:ELS; [done| ]. 
exact ((fst s) -[f0]-> (project_lib_trace tr)).
Defined. 

Definition is_end_state (step: client_state * option (option client_role * client_state)) :=
  exists st, step = (st, None). 

Lemma lib_trace_construction (tr: mtrace client_model_impl)
  (VALID: mtrace_valid tr)
  (LIB_STEPS: ∀ i res, tr !! i = Some res → is_lib_step res \/ is_end_state res):
    lm_model_traces_match
      (inl: lib_grole -> fmrole client_model_impl)
      (fun c δ_lib => fst c = δ_lib)
      tr
      (project_lib_trace tr).
Proof.
  gd tr. cofix IH.
  intros. 
  rewrite (trace_unfold_fold (project_lib_trace tr)).
  rewrite /project_lib_trace.
  destruct tr.
  { econstructor. done. }
  do 2 red.
  pose proof (LIB_STEPS 0 (s, Some (ℓ, (trfirst tr))) eq_refl) as STEP0.
  destruct STEP0 as [STEP0 | STEP0].
  2: { destruct STEP0. done. }
  destruct STEP0 as (?&?&?&[=]&[ρlg <-]). subst. simpl in *. 
  destruct decide.
  { forward eapply (mtrace_valid_steps' VALID 0) as TRANS0; [eauto| ]. 
    inversion TRANS0; subst. 
    eapply locale_trans_alt in LIB_STEP.
    by rewrite -H2 in e. }
Admitted. 


Definition outer_LM_trace_exposing
  (lmtr: auxtrace (LM := client_model)) (mtr: mtrace client_model_impl) :=
  upto_stutter_auxtr lmtr mtr /\
  (∀ n gi, fair_aux_SoU lmtr (inl gi) n) /\
  (* TODO: remove LMo parameter from inner_obls_exposed *)
  inner_obls_exposed inl (λ c δ_lib, c.1 = δ_lib) lmtr (LMo := client_model).

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
Lemma upto_stutter_Proper_impl {St S' L L': Type} {Us: St -> S'} {Ul: L -> option L'}:
  Proper (@traces_equiv St L ==> @traces_equiv S' L' ==> impl)
    (upto_stutter Us Ul).
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

Instance upto_stutter_Proper {St S' L L': Type} {Us: St -> S'} {Ul: L -> option L'}:
  Proper (@traces_equiv St L ==> @traces_equiv S' L' ==> iff)
    (upto_stutter Us Ul).
Proof. 
  red. intros ??????. split.
  - intros. eapply upto_stutter_Proper_impl; eauto.
  - intros. apply traces_equiv_symm in H, H0. 
    eapply upto_stutter_Proper_impl; eauto.
Qed. 
                                   

Lemma outer_exposing_subtrace ltr tr i str 
  (OUTER_CORR: outer_LM_trace_exposing ltr tr)
  (SUB: subtrace tr i NOinfinity = Some str):
  exists sltr, 
    outer_LM_trace_exposing sltr str.
Proof. 
  red in OUTER_CORR. destruct OUTER_CORR as (UPTO & FAIR_AUX & INNER_OBLS).
  pose proof (trace_has_len tr) as [len LEN].
  pose proof SUB as X. eapply subtrace_equiv_after in X as (atr & AFTER & EQUIV); eauto.
  2: { lia_NO len. }
  forward eapply upto_stutter_after; eauto. intros (i' & latr & AFTER' & UPTO').
  exists latr. split; [| split].
  - eauto. eapply upto_stutter_Proper; [.. |eapply UPTO']; eauto.
    + reflexivity. 
    + by symmetry.
  - intros.
    forward eapply fair_aux_SoU_after; [| apply AFTER' |]; eauto.
    intros. apply FAIR_AUX.
  - eapply inner_obls_exposed_after; eauto.
Qed.   

(* TODO: move *)
Lemma trace_len_gt_0 {St L: Type} (tr: trace St L):
  forall len, trace_len_is tr len -> NOmega.lt_nat_l 0 len.
Proof. 
  intros. lia_NO' len. destruct n; [| lia].
  by apply trace_len_0_inv in H. 
Qed. 


(* TODO: move *)
Lemma trace_lookup_0_Some {St L: Type} (tr: trace St L):
  is_Some (tr !! 0). 
Proof.
  pose proof (trace_has_len tr) as [len LEN]. 
  eapply trace_lookup_dom; eauto.
  eapply trace_len_gt_0; eauto. 
Qed.  
  
Local Notation " 'step_of' M " := 
  (fmstate M * option (option (fmrole M) * fmstate M))%type 
    (at level 10).

Lemma client_trace_lookup (tr: mtrace client_model_impl) i
  (VALID: mtrace_valid tr)
  :
  terminating_trace tr \/
  exists step, tr !! i = Some step /\
            (is_client_step step \/
             is_lib_step step /\ snd $ fst step = 1).
Proof.
  pose proof (trace_has_len tr) as [len LEN].
  destruct (tr !! i) as [[st step]|] eqn:ST.
  2: { left. eapply terminating_trace_equiv; eauto.
       eapply trace_lookup_dom_neg in ST; eauto.
       lia_NO' len. eauto. }
  destruct step as [[ℓ st']|].
  2: { pattern st in ST. eapply ex_intro, trace_lookup_dom_eq in ST; eauto.
       left. eapply terminating_trace_equiv; eauto. }
  right. eexists. split; eauto. simpl.
  forward eapply (mtrace_valid_steps' VALID i) as TRANS; [eauto| ].
  simpl in TRANS.
  inversion TRANS; subst.
  1, 3: left; do 2 red; eauto.
  right. split; eauto. do 2 red.
  do 3 eexists. eauto.
Qed. 

(* TODO: try to unify with 'kept_*' lemmas
   in ticketlock proof *)
(* TODO: move*)
Lemma preserved_prop_kept (M: FairModel) (tr: mtrace M)
  (Pst: fmstate M -> Prop)
  (Pstep: step_of M -> Prop)
  (m1 m2 : nat) s
  (VALID : mtrace_valid tr)
  (L2: ∀ i step, m1 ≤ i → i < m2 → tr !! i = Some step → Pstep step)
  (* (PRES: forall s1 ℓ s2, Pstep (s1, Some (ℓ, s2)) -> Pst s1 -> Pst s2) *)
  (PRES: forall s1 ℓ s2, Pstep (s1, Some (ℓ, s2)) -> fmtrans M s1 ℓ s2 -> Pst s1 -> Pst s2)
  (Sm1 : tr S!! m1 = Some s)
  (P1: Pst s):
  (* (C1 : s.2 = 1): *)
  ∀ j s, m1 <= j <= m2 → tr S!! j = Some s → Pst s. 
Proof. 
  intros j s' [GE LE] ST.
  apply Nat.le_sum in GE as [d ->].
  gd s'. induction d.
  { intros. rewrite Nat.add_0_r in LE ST.
    assert (s' = s) as ->; congruence. }
  intros s' ST'.
  pose proof (trace_has_len tr) as [len LEN]. 
  forward eapply (proj2 (trace_lookup_dom_strong _ _ LEN (m1 + d))).
  { eapply mk_is_Some, state_lookup_dom in ST'; eauto.
    lia_NO len. }
  clear dependent s. 
  intros (s & ? & s'_ & STEP'_). 
  forward eapply (mtrace_valid_steps' VALID) as TRANS; [eauto| ].
  pose proof STEP'_ as X%L2; try lia. 
  (* destruct X as (?&?&?&[=]&[? <-]). subst.   *)
  apply state_label_lookup in STEP'_ as (ST & ST'_ & LBL).
  replace (m1 + S d) with (m1 + d + 1) in ST' by lia.
  rewrite ST' in ST'_. inversion ST'_. subst s'_.
  specialize_full IHd; eauto. lia. 
Qed. 

(* TODO: inline? *)
Lemma c1_preserved (tr: mtrace client_model_impl)
  (m1 m2 : nat) s  
  (VALID : mtrace_valid tr)
  (L2: ∀ i res, m1 ≤ i → i < m2 → tr !! i = Some res → is_lib_step res)
  (Sm1 : tr S!! m1 = Some s)
  (C1 : s.2 = 1)
  :
  ∀ j s, m1 <= j <= m2 → tr S!! j = Some s → s.2 = 1.
Proof. 
  eapply preserved_prop_kept; eauto.
  intros ??? LIB STEP EQ1.
  do 2 red in LIB. destruct LIB as (?&?&?&[=]&[? <-]). subst.
  simpl in STEP. inversion STEP. by subst.
Qed.

(* TODO: inline? *)  
Lemma done_lib_preserved (tr: mtrace client_model_impl)
  (m1 m2 : nat) s  
  (VALID : mtrace_valid tr)
  (L2: ∀ i res, m1 ≤ i → i < m2 → tr !! i = Some res → is_client_step res)
  (Sm1 : tr S!! m1 = Some s)
  (NOLIB1 : ls_tmap s.1 (LM := lib_model) !! ρlg = Some ∅):
  ∀ j s, m1 <= j <= m2 → tr S!! j = Some s → ls_tmap s.1 (LM := lib_model) !! ρlg = Some ∅.
Proof. 
  eapply preserved_prop_kept; eauto.
  intros ??? CL STEP EQ1.
  do 2 red in CL. destruct CL as (?&?&?&[=]&[=]). subst. 
  simpl in STEP. inversion STEP; subst; done. 
Qed. 

  
Lemma client_model_fair_term tr lmtr
  (OUTER_CORR: outer_LM_trace_exposing lmtr tr):
  mtrace_fairly_terminating tr.
Proof.
  intros. red. intros VALID FAIR.
  (* destruct (infinite_or_finite tr) as [INF|]; [| done]. *)
  pose proof (trace_has_len tr) as [len LEN]. 

  assert (len = NOnum 1 \/ NOmega.lt_nat_l 1 len /\ snd (trfirst tr) <= 2) as [-> | [LENnz BOUNDc]].
  { pose proof (trace_lookup_0_Some tr) as [[δ0 step0] STEP0].
    destruct step0.
    2: { left. rewrite -(plus_O_n 1).
         eapply trace_lookup_dom_eq; eauto. }
    destruct p. 
    right. split.
    { rewrite -(plus_O_n 1). eapply trace_lookup_dom_strong; eauto. }
    forward eapply (mtrace_valid_steps' VALID 0) as TRANS; [eauto| ].
    apply state_label_lookup in STEP0 as (ST0 & ?&?). 
    rewrite state_lookup_0 in ST0. inversion ST0. rewrite H2. 
    inversion TRANS; subst; simpl; lia. }
  { eapply terminating_trace_equiv; eauto. }

  forward eapply (trace_prop_split tr is_client_step) as [l1 (L1 & NL1 & DOM1)]; eauto.
  { solve_decision. }

  (* assert (exists n1, l1 = NOnum n1 /\ (forall s, tr S!! (n1 - 1) = Some s -> snd s < 2)) as (m1 & LEN1 & BOUNDc').  *)
  assert (exists n1, l1 = NOnum n1) as (m1 & LEN1).
  { 
    destruct l1; eauto.
    forward eapply (subtrace_len tr _ 0 NOinfinity) as SUB1; eauto.
    { done. }
    destruct SUB1 as (str & SUB & LEN1). 
    forward eapply (client_steps_finite str) as (m1 & LEN1' & XX); eauto.
    { eapply (subtrace_valid tr); eauto. }  
    { intros. left. eapply L1; [done| ].
      rewrite -H.
      rewrite -{2}(plus_O_n i). symmetry.
      eapply subtrace_lookup; eauto. done. }
    forward eapply (trace_len_uniq _ _ _ LEN1 LEN1'). done. }

  subst l1. simpl in *. 

  forward eapply (trace_prop_split' tr is_lib_step _ m1)
    as (l2 & L2 & NL2 & LE2 & LE2'); eauto.
  { solve_decision. }

  assert (exists m2, l2 = NOnum m2) as [m2 ->].
  { destruct l2 eqn:L2_EQ; [| by eauto].
    forward eapply (subtrace_len tr _ m1 l2) as SUB2; eauto. 
    1, 2: by lia_NO' l2.
    destruct SUB2 as (str & SUB2 & LEN2).

    forward eapply (lib_trace_construction str) as MATCH. 
    { subst. eapply (subtrace_valid tr); eauto. }
    { subst. intros i res RES.
      pose proof RES as H. 
      eapply mk_is_Some, trace_lookup_dom in H; eauto.
      left. apply (L2 (m1 + i)); [lia| ..]; eauto.
      rewrite -RES. symmetry. 
      eapply subtrace_lookup; eauto. }

    eapply simulation_adequacy_terminate_general' in MATCH; eauto; cycle 1. 
    { admit. }
    {       
      subst. simpl in *.
      forward eapply outer_exposing_subtrace; eauto.
      intros [? EXP'].
      
      eapply inner_LM_trace_fair_aux. 
      2-4: by apply EXP'. 
      - apply _. 
      - subst. eapply infinite_trace_equiv; eauto. 
      - by apply MATCH. 
      - eapply fair_by_subtrace; eauto. }   

    red in MATCH. specialize_full MATCH; eauto.
    { subst. eapply (subtrace_valid tr); eauto. }
    { subst. eapply fair_by_subtrace; eauto. }
    apply (terminating_trace_equiv _ _ LEN2) in MATCH as [??].
    subst. done. }

  simpl in *.
  assert (terminating_trace tr \/ exists step, snd (fst step) = 1 /\ tr !! m2 = Some step /\ is_client_step step /\ ls_tmap step.1.1 (LM := lib_model) !! ρlg = Some ∅) as NEXT. 
  { edestruct (client_trace_lookup tr m2) as [?|STEP]; eauto.
    destruct STEP as [[s step] [STEP [CL | [LIB BOUND]]]].
    2: { eapply NL2 in LIB; done. }  
    edestruct (client_trace_lookup tr m1) as [?|STEP']; eauto.
    destruct STEP' as [step' [STEP' [CL' | [LIB BOUND]]]].
    { eapply NL1 in CL'; done. }
    right. do 2 red in CL. destruct CL as (?&?&?&[=]&[=]).
    subst.
    eexists. apply and_comm, and_assoc. 
    split; [apply STEP|]. simpl.
    apply and_assoc. split; [by do 2 red; eauto| ].
    assert (x.2 = 1).
    { apply state_label_lookup in STEP.
    do 2 red in LIB. destruct LIB as (?&?&?&[=]&[? <-]).
    subst. apply state_label_lookup in STEP'. simpl in *. 
    eapply c1_preserved.
    3: { apply (proj1 STEP'). }
    all: eauto.
    apply STEP. }
    forward eapply (mtrace_valid_steps' VALID m2) as TRANS; eauto.
    simpl in TRANS. inversion TRANS; subst. 
    { done. }
    eauto. }
  
  destruct NEXT as [? | (step & BOUND & STm2 & CL2 & NOlib)]; [done| ].
  forward eapply (trace_prop_split' tr is_client_step _ m2) as [l3 (L3 & NL3 & DOM3)]; eauto.
  { solve_decision. }
  forward eapply (subtrace_len tr _ m2 l3) as SUB3; eauto.
  { lia_NO' l3. apply proj1, le_lt_eq_dec in DOM3 as [?| ->]; [done| ].
    eapply NL3 in STm2; done. }
  { apply DOM3. }
  destruct SUB3 as (str3 & SUB3 & LEN3).
  (* TODO: refactor usages of this lemma  *)
  forward eapply (client_steps_finite str3) as (m3 & LEN3' & BOUND3); eauto.
  { eapply (subtrace_valid tr); [..| apply SUB3]; eauto.
    apply DOM3. }  
  { intros. destruct step0 as [[ℓ s']| ]; eauto. left.
    (* pose proof H as X%trace_lookup_dom_strong.  *)
    assert (NOmega.lt_nat_l (i + 1) (NOmega.sub l3 (NOnum m2))). 
    { eapply trace_lookup_dom_strong; eauto. }
    erewrite @subtrace_lookup in H; eauto.
    eapply L3; [..| apply H]; [lia| ].
    lia_NO l3. }
    
  pose proof (trace_len_uniq _ _ _ LEN3 LEN3').
  lia_NO' l3. inversion H. subst m3.
  forward eapply (client_trace_lookup tr n); eauto.
  intros [? | [stepn [STEPn [CL3 | LIB3]]]]; [done| ..].
  { eapply NL3 in CL3; done. }
  destruct LIB3 as [LIB3 BOUND3'].
  do 2 red in LIB3. destruct LIB3 as (?&?&?&[=]&[? <-]).
  subst. simpl in *.
  destruct DOM3 as [LE3 DOM3].

  enough (ls_tmap x.1 (LM := lib_model) !! x2 = Some ∅).
  2: { apply state_label_lookup in STEPn. 
       eapply done_lib_preserved. 
       6: apply STEPn.
       all: eauto.
       destruct CL2 as (?&?&?&[=]&[=]). subst. simpl.
       eapply state_label_lookup; eauto. }
       
  forward eapply (mtrace_valid_steps' VALID n) as TRANS; eauto.
  simpl in TRANS. inversion TRANS. subst.
  apply fm_live_spec in LIB_STEP.
  eapply LM_map_empty_notlive in LIB_STEP; eauto. done. 
Admitted. 

(* TODO: should directly follow from LM state invariants *)
Lemma client_LM_inner_exposed (auxtr: auxtrace (LM := client_model)):
  inner_obls_exposed (inl: lib_grole -> fmrole client_model_impl)
    (λ c δ_lib, c.1 = δ_lib) auxtr.
Proof. Admitted. 

(* TODO: try to unify it with general lemma.
   The problem is that proving client model trace termination
   now depends on client LM trace with certain properties,
   whereas in original lemma all model traces are required to be terminating. *)
Theorem simulation_adequacy_terminate_client Σ 
        `{hPre: @heapGpreS Σ client_model (@LM_EM_HL _ client_model)} (s: stuckness)
        e1 (s1: fmstate client_model_impl)
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* (∀ mtr: @mtrace Mdl, mtrace_fairly_terminating mtr) -> *)
  rel_finitary (sim_rel client_model) →
  (∀ `{hGS: @heapGS Σ client_model (@LM_EM_HL _ client_model)},
      ⊢ |={⊤}=> LM_init_resource 0%nat (initial_ls (LM := client_model) s1 0%nat)
                 ={⊤}=∗
                 WP e1 @ s; 0%nat; ⊤ {{ v, init_thread_post 0%nat }}
  ) ->
  extrace_fairly_terminating extr.
Proof.
  intros Hfb Hwp Hvex Hfair.
  destruct (infinite_or_finite extr) as [Hinf|] =>//.

  destruct (simulation_adequacy_model_trace
              Σ _ _ e1 s1 extr Hvex Hexfirst Hfb Hwp) as (auxtr&mtr&Hmatch&Hupto).

  (* have Hfairaux := ex_fairness_preserved  *)
  (*                    extr auxtr Hinf Hmatch Hfair. *)
  assert (forall ρ n, fair_aux_SoU auxtr ρ n (LM := client_model)) as FAIR_SOU.
  { eapply exec_fairness_implies_step_or_unassign; eauto.  
    - by apply _.
    - apply match_locale_enabled_states_livetids.
    Unshelve. apply _. }
  assert (forall ρ, fair_aux ρ auxtr) as Hfairaux. 
  { eapply steps_or_unassigned_implies_aux_fairness; eauto.  
    - by apply id_inj. 
    - apply match_locale_enabled_states_livetids. }

  have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux.
  have Hvalaux := traces_match_LM_preserves_validity extr auxtr _ _ _ Hmatch.
  have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.

  (* have Htermtr := Hterm mtr Hmtrvalid Hfairm. *)
  assert (mtrace_fairly_terminating mtr) as FAIR_TERM. 
  { eapply client_model_fair_term.
    red. split; [| split]; eauto.
    apply client_LM_inner_exposed. }
  assert (terminating_trace mtr) as Hterm.
  { eapply FAIR_TERM; eauto. }
    
  eapply traces_match_preserves_termination =>//.
  eapply upto_stutter_finiteness =>//.
Qed.

Theorem client_terminates
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [client #()]):
  (∀ tid, fair_ex tid extr) -> terminating_trace extr.
Proof.
  set (Σ := gFunctors.app (heapΣ (@LM_EM_HL _ client_model)) clientPreΣ). 
  assert (heapGpreS Σ (@LM_EM_HL _ client_model)) as HPreG.
  { apply _. }
  (* eset (δ_lib0: LiveState lib_grole lib_model_impl).  := {| |}). *)
  set (st0 := (δ_lib0, 2)). 
  unshelve eapply (simulation_adequacy_terminate_client Σ NotStuck _ (st0: fmstate client_model_impl) ∅) =>//.
  (* - apply client_model_fair_term.  *)
  - eapply valid_state_evolution_finitary_fairness_simple.
    (* TODO: problems with inferring EqDecision *)
    (* apply client_model_finitary. *)    
    admit. 
  - intros ?. iStartProof.
    rewrite /LM_init_resource. iIntros "!> (Hm & Hfr & Hf) !>". simpl.
    iAssert (|==> frag_free_roles_are ∅)%I as "-#FR".
    { rewrite /frag_free_roles_are. iApply own_unit. }
    iMod "FR" as "FR". 
    iApply (client_spec ∅ δ_lib0 with "[] [Hm Hf FR]"); eauto.
    { set_solver. }
    { simpl.
      (* TODO: make sure that lib can make step in δ_lib0 *)
      admit.  }
    { rewrite /δ_lib0. simpl.
      rewrite build_LS_ext_spec_st build_LS_ext_spec_fuel build_LS_ext_spec_tmap.
      split; try set_solver.
      (* TODO:
         - these roles are actually the same
         - adjust the initial fuel amount *)
      admit. }
    { iApply ActualOwnershipPartial. }
    iFrame.
    iSplitL "FR".
    + (* TODO: fix the initialization theorem so it accepts arbitrary FR set *)
      admit.
    + subst st0.
      iApply has_fuels_proper; [reflexivity| | by iFrame].
      pose proof (live_roles_2 δ_lib0). simpl in H.
      replace (client_lr (δ_lib0, 2)) with ({[inr ρy]}: gset (fmrole client_model_impl)).
      2: { symmetry. apply leibniz_equiv. apply live_roles_2. }
      rewrite -gset_to_gmap_singletons big_opS_singleton. done.
    Unshelve. admit.     
Admitted. 
