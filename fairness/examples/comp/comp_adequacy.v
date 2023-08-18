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
From trillium.fairness.examples.comp Require Import lm_fair my_omega  lemmas trace_len trace_helpers. 

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
  
  

Lemma spinlock_model_finitary (s1 : fmstate client_model_impl):
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

  (* TODO: move *)
  Lemma trace_len_cons s l (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    trace_len_is (s -[l]-> tr) (NOmega.succ len).
  Proof. 
    unfold trace_len_is in *. intros.
    destruct i.
    { simpl. lia_NO' len. simpl. intuition. lia. }
    simpl. rewrite LEN. lia_NO len.
  Qed.
  
  (* TODO: move *)
  Lemma trace_len_uniq (tr: trace St L) (len1 len2: nat_omega)
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
  
  Lemma trace_len_tail s l (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is (s -[l]-> tr) len):
    trace_len_is tr (NOmega.pred len).
  Proof.
    pose proof (trace_has_len tr) as [len' LEN'].
    pose proof (trace_len_cons s l _ _ LEN').
    forward eapply (trace_len_uniq _ _ _ LEN H) as ->; eauto.
    lia_NO' len'. 
  Qed.
  
  (* TODO: move*)
  Lemma trace_state_lookup_simpl (tr: trace St L) i s' step s
    (TLi: tr !! i = Some (s', step))
    (SLi: tr S!! i = Some s):
    s' = s.
  Proof.
    rewrite /state_lookup in SLi. rewrite /lookup /trace_lookup in TLi.
    destruct (after i tr); [destruct t| ]; congruence.
  Qed. 


(* TODO: move to my_omega *)
  Definition le' n m :=
    match n, m with
    | _, NOinfinity => True
    | NOnum n, NOnum m => n <= m
    | _, _ => False
  end.

  CoFixpoint trace_prefix_inf (tr: trace St L) (max_len: nat_omega): trace St L :=
    match tr, max_len with
    | tr, NOnum 0 => ⟨ trfirst tr ⟩ (* shouldn't be reached if max_len > 0*)
    | tr, NOnum 1 => ⟨ trfirst tr ⟩ (* actual base case *)
    | ⟨ s ⟩, _ => ⟨ s ⟩
    | s -[ l ]-> tr', ml => s -[l]-> (trace_prefix_inf tr' (NOmega.pred ml))
    end. 


  (* TODO: move *)
  Global Instance nomega_eqdec: EqDecision nat_omega.
  Proof. solve_decision. Qed. 

  Definition subtrace (tr: trace St L) (start: nat) (fin: nat_omega): option (trace St L) :=
    match (after start tr) with
    | None => None
    | Some tr => let max_len := NOmega.sub fin (NOnum start) in
                if (decide (max_len = NOnum 0))
                then None
                else Some (trace_prefix_inf tr max_len)
    end.

  Lemma trace_prefix_len1 (tr: trace St L):
    trace_prefix_inf tr (NOnum 1) = ⟨ trfirst tr ⟩.
  Proof. 
    rewrite (trace_unfold_fold (trace_prefix_inf tr (NOnum 1))).
    destruct tr; done. 
  Qed. 

  (* TODO: move*)
  (* useful for rewriting in equivalences *)
  Lemma is_Some_Some_True {A: Type} (a: A):
    is_Some (Some a) <-> True.
  Proof. done. Qed. 

  (* TODO: move*)
  (* useful for rewriting in equivalences *)
  Lemma is_Some_None_False {A: Type}:
    is_Some (None: option A) <-> False.
  Proof.
    split; [| done]. by intros []. 
  Qed. 

  (* TODO: move*)
  Lemma trace_len_singleton (s: St):
    trace_len_is ⟨ s ⟩ (NOnum 1) (L := L).
  Proof. 
    red. intros. destruct i; simpl.
    - rewrite is_Some_Some_True. lia.
    - rewrite is_Some_None_False. lia.
  Qed. 

  (* TODO: move*)
  Lemma trace_len_after (tr tr': trace St L) i
    (len: nat_omega)
    (LEN: trace_len_is tr len)
    (AFTER: after i tr = Some tr'):
    trace_len_is tr' (NOmega.sub len (NOnum i)).
  Proof.
    gd tr. gd tr'. gd len. induction i.
    { intros. simpl in AFTER. 
      rewrite NOmega.sub_0_r. inversion AFTER. by subst. }
    intros. destruct tr; [done| ].
    simpl in AFTER.
    pose proof (trace_len_tail _ _ _ _ LEN).
    specialize (IHi _ _ _ H AFTER).
    lia_NO' len. simpl in *.
    by replace (n - S i) with (Nat.pred n - i) by lia.
  Qed. 

  Lemma trace_prefix_inf_len (tr: trace St L) (len max_len: nat_omega)
    (GT0: max_len ≠ NOnum 0)
    (LEN: trace_len_is tr len)
    (LE: le' max_len len)
    :
    trace_len_is (trace_prefix_inf tr max_len) max_len.
  Proof. 
    destruct max_len.
    { lia_NO' len.
      red. simpl. clear -LEN.
      intros i. gd tr. induction i.
      { simpl. done. }
      intros.
      rewrite (trace_unfold_fold (trace_prefix_inf tr NOinfinity)).
      destruct tr.
      { done. }
      specialize (IHi tr). specialize_full IHi.
      { apply trace_len_tail in LEN. eauto. }
      done. }      
    gd tr. gd len. induction n.
    { intros. done. }
    intros. 
    destruct n. 
    { rewrite trace_prefix_len1. apply trace_len_singleton. }
    rewrite (trace_unfold_fold (trace_prefix_inf tr (NOnum (S (S n))))). 
    destruct tr. 
    { pose proof (trace_len_singleton s) as LEN'.
      pose proof (trace_len_uniq _ _ _ LEN LEN').
      subst. simpl in *. lia. }
    specialize (IHn ltac:(done) (NOmega.pred len)).
    specialize (IHn ltac:(lia_NO len)). specialize_full IHn.
    { eapply trace_len_tail; eauto. }
    apply (trace_len_cons s ℓ) in IHn. done.
  Qed. 


  Lemma subtrace_len (tr: trace St L) (len: nat_omega)
    (start: nat) (fin: nat_omega)
    (LEN: trace_len_is tr len)
    (LE: NOmega.lt_nat_l start fin)
    (BOUND: le' fin len):
    exists str, subtrace tr start fin = Some str /\
           trace_len_is str (NOmega.sub fin (NOnum start)).
  Proof. 
    rewrite /subtrace.
    forward eapply (proj2 (LEN start)) as [atr SUF]. 
    { lia_NO' len; lia_NO' fin. }
    rewrite SUF.
    destruct decide. 
    { lia_NO' fin. inversion e. lia. }
    eexists. split; eauto.
    eapply trace_prefix_inf_len; eauto.
    - eapply trace_len_after; eauto.
    - lia_NO' fin; lia_NO len.
  Qed.    

  Lemma subtrace_eq_after (tr atr: trace St L) len start fin
    (LEN: trace_len_is tr len)
    (* (start: nat) *)
    (* (AFTER : after start tr = Some atr) *)
    (* (d : nat_omega) *)
    (* (n : d ≠ NOnum 0): *)
    (* forall k, NOmega.lt_nat_l k d -> trace_prefix_inf atr d !! k = atr !! k.  *)
    (LE: le' len fin):
    subtrace tr start fin = after start tr.
  Proof.
    


  Lemma trace_prefix_inf_lookup_after (tr atr : trace St L)
    (start : nat)
    (AFTER : after start tr = Some atr)
    (d : nat_omega)
    (n : d ≠ NOnum 0):
    forall k, NOmega.lt_nat_l k d -> trace_prefix_inf atr d !! k = atr !! k. 
  Proof.
    pose proof (trace_has_len atr) as [len LEN].
    destruct (decide 
    destruct d. 
    { admit. }
    (* gd tr. *)
    gd atr. gd start. gd k. induction n0.
    { intros. done. }

    
    intros. destruct k.
    { simpl.
      rewrite (trace_unfold_fold (trace_prefix_inf atr (NOnum (S n0)))).
      destruct atr; simpl.  

    
      rewrite (trace_unfold_fold (trace_prefix_inf atr (NOnum (S n0)))).
    destruct atr. 
 
    


  Lemma subtrace_lookup_after (tr: trace St L) str atr
    (start: nat) (fin: nat_omega)
    (SUB: subtrace tr start fin = Some str)
    (AFTER: after start tr = Some atr):
    forall k, str !! k = atr !! k. 
  Proof. 
    intros. rewrite /subtrace in SUB. rewrite AFTER in SUB.
    destruct decide; [done| ].
    inversion SUB. subst. clear SUB. 

    remember (NOmega.sub fin (NOnum start)) as d. clear Heqd fin. 
    
    clegd atr. gd res. 
    
    

  Lemma subtrace_lookup (tr: trace St L) str
    (start: nat) (fin: nat_omega)
    (SUB: subtrace tr start fin = Some str):
    forall k res, str !! k = Some res <-> tr !! (start + k) = Some res.
  Proof. 
    intros. 

  Definition trace_append (tr1 tr2: trace St L): trace St L.
  Admitted.

  (* Definition trace_concat (ltr tr2: list (trace St L)): trace St L :=  *)
  (* Admitted. *)

  Lemma trace_append_terminating (tr1 tr2: trace St L)
    (FIN1: terminating_trace tr1) (FIN2: terminating_trace tr2):
    terminating_trace (trace_append tr1 tr2). 
  Proof. Admitted.

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

  (* TODO: move*)
  Global Instance no_lt_nat_l_dec: forall x y, Decision (NOmega.lt_nat_l x y).
  Proof. 
    intros. destruct y.
    + by left.
    + simpl. solve_decision.
  Qed. 

  Lemma trace_prop_split' (tr: trace St L) (P: (St * option (L * St)) -> Prop)
                          (from: nat) len 
    (DECP: forall res, Decision (P res))
    (LEN: trace_len_is tr len)
    : 
    exists (l: nat_omega), 
    (forall i res (GE: from <= i) (LT: NOmega.lt (NOnum i) l) (RES: tr !! i = Some res), P res) /\
    (forall j res (NEXT: l = NOnum j) (RES: tr !! j = Some res), ¬ P res) /\
    le' l len.
  Proof.
    destruct (decide (NOmega.lt_nat_l from len)) as [LT | GE]. 
    2: { lia_NO' len. exists (NOnum n). repeat split.
         - lia.
         - intros. inversion NEXT. subst.
           forward eapply trace_lookup_dom with (i := j) as [C _]; eauto.
           specialize (C (@ex_intro _ _ _ RES)). simpl in *. lia.
         - simpl. lia. }
    forward eapply subtrace_len as (str & SUB & LEN'); eauto.
    { lia_NO len. }

    forward eapply (trace_prop_split str) as (lim' & PROP & NPROP & LIM'); eauto.
    exists (NOmega.add lim' (NOnum from)). repeat split.
    - intros. apply Nat.le_sum in GE as [d ->]. 
    

End Subtrace.

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


(* TODO: move*)  
Lemma state_lookup_cons s l (tr: mtrace client_model_impl) i:
  (s -[ l ]-> tr) S!! S i = tr S!! i.
Proof. done. Qed. 
    
(* TODO: move*)  
Lemma label_lookup_cons s l (tr: mtrace client_model_impl) i:
  (s -[ l ]-> tr) L!! S i = tr L!! i.
Proof. done. Qed. 

Definition is_client_step := fun step => step_label_matches step (eq (inr ρy)).     
Definition is_lib_step := fun step => step_label_matches step 
                                     (fun ρ => exists ρlg, inl ρlg = ρ).     

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

Arguments le' _ _ : simpl nomatch.

(* TODO: move*)
Lemma trace_len_neg (tr: mtrace client_model_impl) (len: nat_omega)
  (LEN: trace_len_is tr len):
  forall (i: nat), after i tr = None <-> NOmega.le len (NOnum i).
Proof. 
  intros. specialize (LEN i).
  destruct (after i tr).
  - apply proj1 in LEN. specialize_full LEN; eauto. 
    split; try done. lia_NO len.
  - split; try done. intros _.
    lia_NO' len.
    + by destruct (proj2 LEN I).
    + destruct (decide (n <= i)); [done| ].
      by destruct (proj2 LEN ltac:(lia)).
Qed.      


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

  destruct (after m1 tr) as [tr'| ] eqn:TR'.
  2: { eapply trace_len_neg in TR'; eauto.
       lia_NO' len. assert (n = m1) as -> by lia.
       admit. }
  forward eapply (trace_prop_split tr' is_lib_step) as [l2 (L2 & NL2 & DOM2)]; eauto.
  { solve_decision. }
  { eapply trace_len_after; eauto. }
  
  (* set (str_lib := subtrace *)
  pose proof (subtrace_len _ _ m1

    specialize (LEN m1). rewrite TR' in LEN.
       lia_NO' len; intuition; try discriminate. 
       rewrite <- is_Some_None in LEN. 
  clear L1 DOM1.

  
   (trace_prop_split tr _ _  LEN) as [l1 (L1 & NL1 & DOM1)].

  
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
