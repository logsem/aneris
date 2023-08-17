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

From trillium.fairness Require Import fuel_ext. 
From trillium.fairness.examples.comp Require Import comp.
From trillium.fairness Require Import fair_termination_natural.
From trillium.fairness.examples.comp Require Import my_omega  lemmas trace_len trace_helpers. 

Close Scope Z_scope. 

Instance client_trans'_PI s x: 
  ProofIrrel ((let '(s', ℓ) := x in 
               fmtrans client_model_impl s ℓ s' \/ (s' = s /\ ℓ = None)): Prop).
Proof. apply make_proof_irrel. Qed.    
  
Lemma spinlock_model_finitary (s1 : client_model_impl):
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

(* TODO: move*)
Section Subtrace.
  Context {St L: Type}.

  Definition subtrace (tr_sub tr: trace St L) (start: nat) (fin: nat_omega): Prop.
  Admitted. 

  Definition trace_append (tr1 tr2: trace St L): trace St L.
  Admitted.

  (* Definition trace_concat (ltr tr2: list (trace St L)): trace St L :=  *)
  (* Admitted. *)

  Lemma trace_append_terminating (tr1 tr2: trace St L)
    (FIN1: terminating_trace tr1) (FIN2: terminating_trace tr2):
    terminating_trace (trace_append tr1 tr2). 
  Proof. Admitted.

(* TODO: move to my_omega *)
Definition le' n m :=
  match n, m with
  | _, NOinfinity => True
  | NOnum n, NOnum m => n <= m
  | _, _ => False
  end.

  (* TODO: move *)
  Require Import Coq.Logic.Classical.
  Lemma trace_prop_split (tr: trace St L) (P: (St * option (L * St)) -> Prop) len 
    (DECP: forall res, Decision (P res))
    (LEN: trace_len_is tr len)
    : 
    (* (forall i res, tr !! i = Some res -> P res) \/ *)
    (* exists (l: nat), forall i (LT: NOmega.lt (NOnum i) l), *)
    (*   pred_at tr i /\ (exists m, l = NOnum m -> pred_ *)
    (*   pred_at *)
    exists (l: nat_omega), 
    (forall i res (LT: NOmega.lt (NOnum i) l) (RES: tr !! i = Some res), P res) /\
    (forall j res (NEXT: l = NOnum j) (RES: tr !! j = Some res), ¬ P res) /\
    le' l len. 
  Proof using.
    destruct (classic (exists j res, tr !! j = Some res /\ ¬ P res)) as [STOP | EV]. 
    - destruct STOP as [j' STOP'].
      pattern j' in STOP'. apply min_prop_dec in STOP' as [j [NPROP MIN]]. 
      2: { intros. admit. }
      exists (NOnum j). simpl in *. repeat split.      
      + intros. destruct (decide (P res)); [done| ]. 
        enough (j <= i); [lia| ].
        apply MIN. eexists. split; eauto.
      + intros. inversion NEXT. subst.
        destruct NPROP as [? [RES' NP]].
        congruence.
      + lia_NO' len.
        destruct NPROP as [? [RES' NP]].
        pose proof (proj1 (trace_lookup_dom _ _ LEN j) (ex_intro _ x RES')).
        simpl in H. lia. 
    - exists len. repeat split.
      + intros.
        apply not_exists_forall_not with (x := i) in EV. 
        apply not_exists_forall_not with (x := res) in EV.
        apply not_and_or in EV. destruct EV; [done| ].
        eapply NNP_P; eauto.
      + intros.
        apply not_exists_forall_not with (x := j) in EV.        
        pose proof (proj1 (trace_lookup_dom _ _ LEN j)).
        specialize (H ltac:(eauto)).
        lia_NO' len. inversion NEXT. lia.
      + lia_NO len. 
  Admitted. 

End Subtrace.

Definition is_client_step (step: client_state * option (option client_role * client_state)) :=
  exists st1 st2, step = (st1, Some (Some $ inr ρy, st2)). 

Instance ics_dec: forall step, Decision (is_client_step step).
Proof. 
  rewrite /is_client_step. intros [? p2].
  destruct p2 as [p2| ]. 
  2: { right. by intros (?&?&?). }
  destruct p2 as [or s2].
  destruct or as [r |]. 
  2: { right. by intros (?&?&?). }
  destruct (decide (r = inr ρy)).
  - left. subst. do 2 eexists. eauto.
  - right. intros (?&?&?). congruence.
Qed. 


Local Ltac gd t := generalize dependent t.

(* TODO: move *)
Lemma trace_len_cons s l (tr: mtrace client_model_impl) (len: nat_omega)
  (LEN: trace_len_is tr len):
  trace_len_is (s -[l]-> tr) (NOmega.succ len).
Proof. 
  unfold trace_len_is in *. intros.
  destruct i.
  { simpl. lia_NO' len. simpl. intuition. lia. }
  simpl. rewrite LEN. lia_NO len.
Qed.

(* TODO: move *)
Lemma trace_len_uniq (tr: mtrace client_model_impl) (len1 len2: nat_omega)
  (LEN1: trace_len_is tr len1) (LEN2: trace_len_is tr len2):
  len1 = len2. 
Proof. 
  unfold trace_len_is in *.
  destruct (NOmega_trichotomy len1 len2) as [?|[?|?]]; auto.
  - destruct len1; [done| ].
    pose proof (proj2 (LEN2 n)) as L2. specialize (L2 ltac:(lia_NO len2)).
    specialize (proj1 (LEN1 _) L2). simpl. lia.
  - destruct len2; [done| ].
    pose proof (proj2 (LEN1 n)) as L1. specialize (L1 ltac:(lia_NO len1)).
    specialize (proj1 (LEN2 _) L1). simpl. lia.
Qed. 

Lemma trace_len_tail s l (tr: mtrace client_model_impl) (len: nat_omega)
  (LEN: trace_len_is (s -[l]-> tr) len):
  trace_len_is tr (NOmega.pred len).
Proof.
  pose proof (trace_has_len tr) as [len' LEN'].
  pose proof (trace_len_cons s l _ _ LEN').
  forward eapply (trace_len_uniq _ _ _ LEN H) as ->; eauto.
  lia_NO' len'. 
Qed.

(* TODO: move *)
Global Instance nomega_eqdec: EqDecision nat_omega.
Proof. solve_decision. Qed. 

(* TODO: move*)
Lemma trace_state_lookup_simpl (tr: mtrace client_model_impl) i s' step s
  (TLi: tr !! i = Some (s', step))
  (SLi: tr S!! i = Some s):
  s' = s.
Proof.
  rewrite /state_lookup in SLi. rewrite /lookup /trace_lookup in TLi.
  destruct (after i tr); [destruct t| ]; congruence.
Qed. 

(* TODO: move*)  
Lemma state_lookup_cons s l (tr: mtrace client_model_impl) i:
  (s -[ l ]-> tr) S!! S i = tr S!! i.
Proof. done. Qed. 
    
(* TODO: move*)  
Lemma label_lookup_cons s l (tr: mtrace client_model_impl) i:
  (s -[ l ]-> tr) L!! S i = tr L!! i.
Proof. done. Qed. 
    

Lemma client_steps_finite (tr: mtrace client_model_impl) (l len: nat_omega)
  (VALID: mtrace_valid tr)
  (LEN: trace_len_is tr len)
  (LE: le' l len)
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
  { specialize (CL _ _ I L0). red in CL. destruct CL as (?&?&?).
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


Lemma client_model_fair_term:
  ∀ tr: mtrace client_model_impl, mtrace_fairly_terminating tr.
Proof.
  intros. red. intros VALID FAIR.
  (* destruct (infinite_or_finite tr) as [INF|]; [| done]. *)
  pose proof (trace_has_len tr) as [len LEN]. 
  pose proof (trace_prop_split tr _ _ ics_dec LEN) as [l1 (L1 & NL1 & DOM1)].
  forward eapply client_steps_finite as [m1 ?]; eauto. subst l1. simpl in *.   
  
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
  unshelve eapply (simulation_adqeuacy_terminate Σ NotStuck _ (st0: fmstate client_model_impl) ∅) =>//.
  - apply client_model_fair_term. 
  - eapply valid_state_evolution_finitary_fairness_simple.
    apply spinlock_model_finitary.
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
