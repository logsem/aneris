From trillium.fairness Require Import inftraces trace_lookup fairness trace_len my_omega.


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

