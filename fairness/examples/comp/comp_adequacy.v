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

  assert (exists n1, l1 = NOnum n1 /\ (forall s, tr S!! (n1 - 1) = Some s -> snd s < 2)) as (m1 & LEN1 & BOUNDc'). 
  { 
    (* destruct l1; eauto.  *)
    forward eapply (subtrace_len tr _ 0 l1) as SUB1; eauto.
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

  
  
Admitted. 

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
  unshelve eapply (simulation_adequacy_terminate Σ NotStuck _ (st0: fmstate client_model_impl) ∅) =>//.
  - apply client_model_fair_term. 
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
Admitted. 
