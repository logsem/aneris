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

From trillium.fairness Require Import lm_fairness_preservation.
From trillium.fairness Require Import fuel_ext. 
From trillium.fairness.examples.comp Require Import comp.
From trillium.fairness Require Import fair_termination_natural.
From trillium.fairness.examples.comp Require Import lm_fair my_omega lemmas trace_len trace_helpers subtrace trace_lookup.

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

Lemma client_steps_finite (tr: mtrace client_model_impl) (l len: nat_omega)
  (VALID: mtrace_valid tr)
  (LEN: trace_len_is tr len)
  (LE: NOmega.le l len)
  (CL: ∀ i res, NOmega.lt (NOnum i) l → tr !! i = Some res → is_client_step res):
  exists m, l = NOnum m.
Proof.
  lia_NO' l; lia_NO' len; try by eauto. exfalso.
  assert (exists s0, tr S!! 0 = Some s0) as [[δ0 c0] S0].
  { pose proof (inf_trace_lookup _ LEN 0) as ([δ0 c0] & ℓ0 & s1 & L0).
    apply state_label_lookup in L0 as (?&?&?). eauto. } 
  gd tr. gd δ0. clear LE. induction c0.
  { intros.
    pose proof (inf_trace_lookup _ LEN 0) as (? & ℓ & ? & L0).
    forward eapply trace_state_lookup_simpl as EQ; eauto. subst x.  
    pose proof (mtrace_valid_steps' VALID _ _ _ _ L0) as S. by inversion S. }
  intros. destruct tr.
  { specialize (LEN 1). simpl in *.
    by pose proof (proj2 LEN I) as []. }
  pose proof (inf_trace_lookup _ LEN 0) as (? & ? & [δ1 c1] & L0).
  forward eapply trace_state_lookup_simpl as EQ; eauto. subst x.  
  pose proof (mtrace_valid_steps' VALID _ _ _ _ L0).
  assert (c1 = c0) as ->.
  { specialize (CL _ _ I L0). do 2 red in CL. destruct CL as (?&?&?&[? <-]).
    inversion H0. subst. clear H0. 
    inversion H; lia. }
  
  assert (tr S!! 0 = Some (δ1, c0)) as L1.
  { apply state_label_lookup in L0 as (_&?&_).
    rewrite Nat.add_1_r in H0. by rewrite state_lookup_cons in H0. }

  eapply (IHc0 δ1 tr); eauto.  
  { eapply mtrace_valid_cons; eauto. }
  { by apply trace_len_tail in LEN. }
  intros. apply (CL (S i)); [done| ].
  rewrite trace_lookup_cons; eauto. 
Qed. 

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


(* TODO: move *)
Definition FM_strong_lr (FM: FairModel) :=
  forall st ρ, ρ ∈ live_roles FM st <-> exists st', fmtrans FM st (Some ρ) st'.

(* TODO: move *)
Lemma lib_model_impl_lr_strong: FM_strong_lr lib_model_impl.
Proof. 
  red. intros.
Admitted. 

Lemma client_model_fair_term:
  ∀ tr: mtrace client_model_impl, mtrace_fairly_terminating tr.
Proof.
  intros. red. intros VALID FAIR.
  (* destruct (infinite_or_finite tr) as [INF|]; [| done]. *)
  pose proof (trace_has_len tr) as [len LEN]. 

  forward eapply (trace_prop_split tr is_client_step) as [l1 (L1 & NL1 & DOM1)]; eauto.
  { solve_decision. } 
  forward eapply client_steps_finite as [m1 ?]; eauto. subst l1. simpl in *.
  (* TODO: also derive the fact that client's counter has decreased *)

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

    eapply simulation_adequacy_terminate_general in MATCH; eauto; cycle 1. 
    { admit. }
    { apply _. }
    { red. intros. destruct c as [? n]. simpl in *. subst.
      red. 
      assert (n = 1) as ->.
      { admit. }
      Set Printing Coercions.
      rewrite live_roles_1.

      (* should be provable with parametrized LiveState
         and connection between tr and corresponding LM trace *)
      admit. }      

    red in MATCH. specialize_full MATCH; eauto.
    { subst. eapply (subtrace_valid tr); eauto. }
    { subst. eapply fair_by_subtrace; eauto. }
    apply (terminating_trace_equiv _ _ LEN2) in MATCH as [??].
    subst. done. }    
  
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
