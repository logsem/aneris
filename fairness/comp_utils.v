From trillium.fairness Require Import inftraces trace_lookup fairness trace_len my_omega fuel lm_fair fairness_finiteness lm_fair_traces lm_fairness_preservation lm_fairness_preservation_wip subtrace traces_equiv.
From trillium.fairness.ext_models Require Import ext_models.
From stdpp Require Import finite.
From trillium.prelude Require Import classical_instances finitary.


Section StepLabelMatches.
  Context {St L: Type}.

  (* TODO: move *)
  Definition trace_step: Type := St * option (L * St). 

  Definition step_label_matches (step: trace_step) (P: L -> Prop) :=
    exists st1 ℓ st2, step = (st1, Some (ℓ, st2)) /\ P ℓ.
   
  Instance slm_dec P (DECP: forall ρ, Decision (P ρ)):
    forall step, Decision (step_label_matches step P).
  Proof. 
    rewrite /step_label_matches. intros [? p2].
    destruct p2 as [p2| ]. 
    2: { right. intros (?&?&?&?). intuition. congruence. }
    destruct p2 as [ℓ s2].
    destruct (decide (P ℓ)).
    - left. subst. do 2 eexists. eauto.
    - right. intros (?&?&?&?). intuition. congruence. 
  Qed. 

  Definition is_end_state (step: trace_step) :=
    exists st, step = (st, None). 

End StepLabelMatches.

Definition model_trace_step (M: FairModel) := 
  @trace_step (fmstate M) (option $ fmrole M). 


Section ProjectNestedTrace.
  
  Context {St L: Type}.
  Context {St' L': Type}.
  Context (proj_st: St -> St') (proj_lbl: L -> option L'). 
  
  CoFixpoint project_nested_trace (tr: trace St L): trace St' L' :=
    match tr with 
    | ⟨ s ⟩ => ⟨ proj_st s ⟩
    | s -[ ℓ ]-> tr' =>
        match proj_lbl ℓ with
        | Some ℓ' => (proj_st s) -[ ℓ' ]-> (project_nested_trace tr')
        | None => ⟨ proj_st s ⟩
        end
    end. 

  Lemma project_nested_trfirst (tr: trace St L):
    trfirst (project_nested_trace tr) = proj_st (trfirst tr).
  Proof. 
    destruct tr; eauto. simpl.
    by destruct proj_lbl. 
  Qed. 

  Local Ltac gd t := generalize dependent t.

  Lemma nested_trace_construction (tr: trace St L)
    (trans: St -> L -> St -> Prop) (trans': St' -> L' -> St' -> Prop)
    (VALID: trace_valid trans tr)
    (NESTED_STEPS: ∀ i res, tr !! i = Some res → 
                         (* is_lib_step res \/ *)
                         step_label_matches res (is_Some ∘ proj_lbl) \/
                         is_end_state res)
    (NESTED_TRANS: forall s1 ℓ s2 ℓ', trans s1 ℓ s2 -> proj_lbl ℓ = Some ℓ' ->
                                  trans' (proj_st s1) ℓ' (proj_st s2)):
    (* True.  *)
    traces_match
      (* (transA := @ext_trans _ ExtLibLM) *)
      (* ((option_fmap _ _ inl): option (@ext_role _ ExtLibLM) -> option $ fmrole client_model_impl) *)
      (* (fun c δ_lib => fst c = δ_lib) *)
      (* tr *)
      (* (project_lib_trace tr). *)
      (fun ℓ ℓ' => proj_lbl ℓ = Some ℓ') (fun st st' => proj_st st = st')
      trans trans'
      tr (project_nested_trace tr).
  Proof.
    gd tr. cofix IH.
    intros. 
    rewrite (trace_unfold_fold (project_nested_trace tr)).
    destruct tr.
    { econstructor. done. }
    (* do 2 red. *)
    pose proof (NESTED_STEPS 0 (s, Some (ℓ, (trfirst tr))) eq_refl) as STEP0.
    destruct STEP0 as [STEP0 | STEP0].
    2: { destruct STEP0. done. }
    destruct STEP0 as (?&?&?&[=]&[ℓ' PROJ]). subst. simpl in *.
    pose proof (trace_valid_cons_inv _ _ _ _ VALID) as [VALID' STEP].
    rewrite PROJ. econstructor.
    1-3: done.
    { rewrite project_nested_trfirst. eauto. }
    eapply IH; eauto. intros. 
    apply (NESTED_STEPS (S i)); eauto. 
  Qed.

End ProjectNestedTrace.


(* TODO: try to unify with 'kept_*' lemmas
   in ticketlock proof *)
(* TODO: move*)
Lemma preserved_prop_kept (M: FairModel) (tr: mtrace M)
  (Pst: fmstate M -> Prop)
  (Pstep: model_trace_step M -> Prop)
  (m1 m2 : nat) s
  (VALID : mtrace_valid tr)
  (L2: ∀ i step, m1 ≤ i → i < m2 → tr !! i = Some step → Pstep step)
  (PRES: forall s1 ℓ s2, Pstep (s1, Some (ℓ, s2)) -> fmtrans M s1 ℓ s2 -> Pst s1 -> Pst s2)
  (Sm1 : tr S!! m1 = Some s)
  (P1: Pst s):
  ∀ j s, m1 <= j <= m2 → tr S!! j = Some s → Pst s. 
Proof. 
  intros j s' [GE LE] ST.
  apply Nat.le_sum in GE as [d ->].
  generalize dependent s'. induction d.
  { intros. rewrite Nat.add_0_r in LE ST.
    assert (s' = s) as ->; congruence. }
  intros s' ST'.
  pose proof (trace_has_len tr) as [len LEN]. 
  forward eapply (proj2 (trace_lookup_dom_strong _ _ LEN (m1 + d))).
  { eapply mk_is_Some, state_lookup_dom in ST'; eauto.
    lia_NO len. }
  clear dependent s. 
  intros (s & ? & s'_ & STEP'_). 
  forward eapply (trace_valid_steps' _ _ VALID) as TRANS; [eauto| ].
  pose proof STEP'_ as X%L2; try lia. 
  (* destruct X as (?&?&?&[=]&[? <-]). subst.   *)
  apply state_label_lookup in STEP'_ as (ST & ST'_ & LBL).
  replace (m1 + S d) with (m1 + d + 1) in ST' by lia.
  rewrite ST' in ST'_. inversion ST'_. subst s'_.
  specialize_full IHd; eauto. lia. 
Qed.


Section LSI_GF_Properties.
  Context `{Countable G}.
  Context {gs: gset G} `(LM: LiveModel G M (LSI_groups_fixed gs)). 
  
  Global Instance LSI_gf_ls_inh (NE: gs ≠ ∅):
    Inhabited (lm_ls LM).
  Proof.
    apply finitary.set_choose_L' in NE as [g GS]. 
    pose proof (fmstate_inhabited M) as [s].
    eapply populate, (initial_ls' s g).
    red. simpl. red. rewrite dom_singleton. set_solver. 
  Qed.
  
  Lemma LSI_gf_rrm (δ1 δ2 : lm_ls LM) τ
    (STEP: locale_trans δ1 τ δ2 (LM := LM)):
    LSI_groups_fixed gs δ2 (rearrange_roles_map (ls_tmap δ2) (dom (ls_tmap δ1)) τ)
      (ls_fuel δ2).
  Proof. 
    red. intros ?. 
    rewrite /rearrange_roles_map. rewrite dom_insert.
    intros [->%elem_of_singleton | IN]%elem_of_union; apply (ls_inv δ1).
    { eapply locale_trans_dom; eauto. }
    by apply dom_filter_sub in IN.
  Qed.
  
  Global Instance LSI_gf_fin_dec_ex_step
    `{EqDecision (fmstate M)}
    `{∀ s1 ρ s2, Decision (fmtrans M s1 (Some ρ) s2)}
    (FIN: ∀ s1, {l : list (fmstate M) | ∀ s2 oρ, fmtrans M s1 oρ s2 → s2 ∈ l}):
    ∀ (τ : G) (δ1 : lm_ls LM),
      Decision (∃ δ2, locale_trans δ1 τ δ2).
  Proof.
    intros. eapply locale_trans_fin_ex_dec_fin; eauto. 
    intros. eexists. eapply rearrange_roles_spec.
    Unshelve.
    + exact LM.
    + by apply LSI_gf_rrm. 
  Defined.

End LSI_GF_Properties.


Section OuterExposing.
  Context `{Countable Go} `{LMo: LiveModel Go Mo LSIo}.
  Context `{Countable Gi} `{LMi: LiveModel Gi Mi LSIi}. 
  Context {LFi: LMFairPre LMi} {LFo: LMFairPre LMo}. 
  Context `{ELMi: ExtModel (LM_Fair (LF := LFi)) EI_LM}.

  Context (EXT_KEEPS: ext_keeps_asg (ELM := ELMi)). 
  Let ALMi := ELM_ALM EXT_KEEPS. 

  Definition outer_LM_trace_exposing
    (* TODO: these functions are closely related, but due to 'option's here and there
       it's hard to express one in terms of another.
       We should just get rid of 'option' in FairModel transition. *)
    (lift_Gi: Gi -> fmrole Mo)
    (lift_EAi: option (@ext_role (LM_Fair (LF := LFi)) EI_LM) -> option (fmrole Mo))
    (state_rel : Mo → lm_ls LMi → Prop)
    
    (lmtr: lmftrace (LM := LMo)) (mtr: mtrace Mo)
    :=
    upto_stutter_auxtr lmtr mtr /\
      (∀ gi, fair_aux_SoU _ (lift_Gi gi) lmtr) /\
      (* TODO: get rid of LMo and use appropriate fairness premise on mtr *)
      inner_obls_exposed lift_EAi state_rel lmtr (LMo := LMo) (AMi := ALMi).
  
  Lemma outer_exposing_subtrace_gen ltr tr i str
    lift_Gi lift_EAi state_rel
    (OUTER_CORR: outer_LM_trace_exposing lift_Gi lift_EAi state_rel ltr tr)
    fin
    (SUB: subtrace tr i fin = Some str)
    len
    (LEN: trace_len_is tr len)
    (GE_LEN: NOmega.le len fin):    
    exists sltr, 
      outer_LM_trace_exposing lift_Gi lift_EAi state_rel sltr str.
  Proof. 
    red in OUTER_CORR. destruct OUTER_CORR as (UPTO & FAIR_AUX & INNER_OBLS).
    pose proof SUB as X.
    unshelve eapply subtrace_equiv_after in X as (atr & AFTER & EQUIV); eauto.  
    forward eapply upto_stutter_after; eauto. intros (i' & latr & AFTER' & UPTO').
    exists latr. split; [| split].
    - eauto. eapply upto_stutter_Proper; [.. |eapply UPTO']; eauto.
      + reflexivity. 
      + by symmetry.
    - intros.
      forward eapply fair_by_gen_after; [apply AFTER' |..]; eauto.
      intros. apply FAIR_AUX.
    - eapply inner_obls_exposed_after; eauto.
  Qed.

  Lemma outer_exposing_subtrace ltr tr i str
    lift_Gi lift_EAi state_rel
    (OUTER_CORR: outer_LM_trace_exposing lift_Gi lift_EAi state_rel ltr tr)
    (SUB: subtrace tr i NOinfinity = Some str):    
    exists sltr, 
      outer_LM_trace_exposing lift_Gi lift_EAi state_rel sltr str.
  Proof.
    pose proof (trace_has_len tr) as [len LEN].
    eapply outer_exposing_subtrace_gen; eauto.
    lia_NO len. 
  Qed.
  
  Lemma outer_exposing_after ltr tr i atr
    lift_Gi lift_EAi state_rel
    (OUTER_CORR: outer_LM_trace_exposing lift_Gi lift_EAi state_rel ltr tr)
    (AFTER: after i tr = Some atr):
    exists sltr, 
      outer_LM_trace_exposing lift_Gi lift_EAi state_rel sltr atr.
  Proof.
    pose proof (trace_has_len tr) as [len LEN].
    forward eapply subtrace_len with (start := i); eauto. 
    2: reflexivity.
    { apply state_lookup_after_0 in AFTER.
      eapply mk_is_Some, state_lookup_dom in AFTER; eauto. }

    intros (str & SUB & LENs).
    pose proof SUB as SUB_. 
    eapply subtrace_equiv_after in SUB; eauto.
    2: reflexivity.
    destruct SUB as (atr_ & AFTER_ & EQ).
    rewrite AFTER_ in AFTER. inversion AFTER. subst.

    apply traces_equiv_eq in EQ as ->.
    eapply outer_exposing_subtrace_gen; eauto.
    reflexivity. 
  Qed.
  
End OuterExposing.


Section FinitaryModels.
  Context {M: FairModel}.  
  
  Definition model_step_helper
    (st: fmstate M) (step: fmstate M * option (fmrole M)) :=
    let '(s', ℓ) := step in
    fmtrans M st ℓ s' \/ (s' = st /\ ℓ = None).

  Instance model_trans'_PI st step: 
    ProofIrrel (model_step_helper st step). 
  Proof. apply make_proof_irrel. Qed.

  Instance step'_eqdec: 
    forall s1, EqDecision {step | model_step_helper s1 step}.
  (* TODO: why it stopped being inferred automatically? *)
  Proof. 
    pose proof (fmstate_eqdec M).
    solve_decision. 
  (* Qed. *)
  Defined.

  Definition next_states (s1: fmstate M) :=
    {l: list (fmstate M) | forall s2 oρ, fmtrans M s1 oρ s2 -> s2 ∈ l}. 

  Lemma model_finitary_helper (s1: fmstate M)
    (NEXTS: next_states s1)
    :
    Finite {step | model_step_helper s1 step }. 
  Proof.
    rewrite /model_step_helper.
    destruct NEXTS as [nexts ?]. 
    set (steps :=
           let lr := None :: (Some <$> (elements $ live_roles _ s1)) in
           (s1, None) :: (s ← nexts; ρ ← lr; mret (s, ρ))).
   (* : list (lf * nat * option client_role) *)
    eapply in_list_finite with (l := steps).
    intros [s2 oρ] TRANS. destruct TRANS as [TRANS | [EQ ->]].
    2: { set_solver. }
    subst steps. simpl. apply elem_of_cons. right.
    apply elem_of_list_bind. eexists. split; eauto.
    destruct oρ.
    2: { set_solver. }
    apply elem_of_cons. right.
    apply elem_of_list_bind. eexists. split. 
    { apply elem_of_list_ret. reflexivity. }
    apply elem_of_list_fmap_1, elem_of_elements.
    eapply fm_live_spec; eauto.
  Qed. 

End FinitaryModels.


Section BoundedLM.
  Context `{Countable G} `{LM: LiveModel G M LSI}.
  Context {LFP: LMFairPre LM}.

  Context {nexts_M: forall s1, @next_states M s1}.
  Context {gs: gset G} {G_FIX: forall st tm fm, LSI st tm fm -> LSI_groups_fixed gs st tm fm}.
  Context {LSI_DEC: ∀ st tm fm, Decision (LSI st tm fm)}. 

  Lemma LM_step_fin (δ: lm_ls LM):
    @next_states (LM_Fair (LF := LFP)) δ. 
  Proof.
    pose proof (nexts_M (ls_under δ)) as [next_sts NEXT_STS].
    pose proof (role_LM_step_dom_all δ ((ls_under δ) :: next_sts) (elements gs) (LM := LM)) as STEPS.
    remember (map fst (enumerate_next δ ((ls_under δ) :: next_sts) (elements gs) (LM := LM))) as nexts. 
    exists nexts. 
    intros δ' oρ TRANS. simpl in TRANS.
    subst nexts.
    destruct oρ as [g| ]; [| done]. simpl in TRANS. 
    simpl in TRANS. destruct TRANS as (ℓ & TRANS & MATCH). 
    apply elem_of_list_In. eapply STEPS; eauto.
    2: { rewrite list_to_set_elements_L. eapply G_FIX. apply δ'. } 
    apply elem_of_cons. 
    edestruct @locale_trans_fmtrans_or_eq as [[? FM] | EQ]. 
    { eexists. eauto. }
    + right. eauto.
    + by left.
  Qed. 

End BoundedLM.
