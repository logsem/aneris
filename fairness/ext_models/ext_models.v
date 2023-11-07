From trillium.fairness Require Import fairness fair_termination.
From trillium.fairness.examples.ticketlock Require Import set_map_properties. 
From trillium.fairness Require Import trace_helpers lm_fairness_preservation lm_fair fuel trace_len.

Class ExtModel (innerM: FairModel) := {  
  EI: Type; (* indexes over external transitions *)
  DecEI: EqDecision EI;
  CntEI: Countable EI;
  ETs: EI -> relation (fmstate innerM);
  (* Ensures that in any state there is only a finite amount 
     of possible external transitions, even if EI is infinite *)
  active_exts: fmstate (innerM) -> gset EI;
  active_exts_spec: forall st ι, ι ∈ active_exts st <-> ∃ st', ETs ι st st';
}.

(* TODO: can it be generalized to Model? *)
Section ExtModelFair.
  Context `{EM: ExtModel innerM}. 

  Inductive env_role := env (i: EI).
  Definition ext_role: Type := (fmrole innerM + env_role). 

  Global Instance env_role_EqDec: EqDecision env_role. 
  Proof using. generalize DecEI. solve_decision. Qed. 

  Global Instance env_role_cnt: Countable env_role. 
  Proof using.
    unshelve refine {| 
        encode r := match r with | env i => encode i end;
        decode i := match (decode i) with | Some r => Some (env r) | None => None end
      |}; try by apply EM. 
    intros. destruct x.
    by rewrite decode_encode.
  Qed.

  Inductive ext_trans: fmstate innerM -> option ext_role -> fmstate innerM -> Prop :=
  | ext_model_step s1 ρ s2 (STEP: fmtrans innerM s1 (Some ρ) s2):
    ext_trans s1 (Some (inl ρ)) s2
  | ext_ext_step s1 s2 ι (REL: ETs ι s1 s2):
    ext_trans s1 (Some (inr (env ι))) s2. 

  Definition ext_live_roles (st: fmstate innerM): gset ext_role :=
    set_map inl (live_roles innerM st) ∪
    set_map (inr ∘ env) (active_exts st). 

  Lemma ext_live_spec:
    ∀ s ρ s', ext_trans s (Some ρ) s' → ρ ∈ ext_live_roles s.
  Proof using.
    intros s ρ s' TRANS. unfold ext_live_roles.
    inversion TRANS; subst; simpl in *.
    - apply elem_of_union_l. apply elem_of_map_2. 
      eapply fm_live_spec; eauto. 
    - apply elem_of_union_r.
      unshelve erewrite set_map_compose_gset; [apply EM| ]. 
      do 2 apply elem_of_map_2.
      apply active_exts_spec. eauto.
  Qed.
  
  Definition ext_model_FM: FairModel.
  Proof using All. 
    refine({|
              fmstate := fmstate innerM;
              fmrole := ext_role;
              fmtrans := ext_trans;
              live_roles := ext_live_roles;
              fm_live_spec := ext_live_spec
            |}).
    apply innerM. 
  Defined.

  Definition inner_fair_ext_model_trace :=
    set_fair_model_trace (λ ρ0: fmrole ext_model_FM, ∃ r, ρ0 = inl r).

  Definition emtrace := trace (fmstate innerM) (option ext_role). 

  Definition emtrace_valid := trace_valid ext_trans. 

End ExtModelFair. 


Definition trans_bounded {St L: Type} (tr: trace St L) (P: L -> Prop) :=
  exists n, forall i ℓ, n <= i -> tr L!! i = Some ℓ -> ¬ P ℓ.

Lemma fin_trans_bounded {St L: Type} (tr: trace St L) (P: L -> Prop)
  (FIN: terminating_trace tr):
  trans_bounded tr P.
Proof.
  pose proof (trace_has_len tr) as [? LEN].
  eapply terminating_trace_equiv in FIN as [n ?]; eauto. subst. 
  red. exists n. intros.
  eapply mk_is_Some, label_lookup_dom in H0; eauto.
  simpl in *. lia.
Qed. 

Section TraceProjection.
  Context {St L St' L': Type}.
  Context (proj_st: St -> St'). 
  Context (proj_lbl: L -> option L'). 

  CoFixpoint project_trace_until (tr: trace St L): trace St' L'
  (* @atrace _ _ _ lib_model (option $ ext_role (EM := ExtLibLM)) *)
  :=
  match tr with 
  | ⟨ s ⟩ => ⟨ proj_st s ⟩
  | s -[ℓ]-> tr' => match (proj_lbl ℓ) with
                  | Some l => (proj_st s) -[ l ]-> (project_trace_until tr')
                  | None => ⟨ proj_st s ⟩
                  end
  end. 

  Lemma project_until_trfirst (tr: trace St L):
    trfirst (project_trace_until tr) = proj_st (trfirst tr).
  Proof. 
    destruct tr; eauto. simpl. 
    destruct (proj_lbl ℓ); eauto. 
  Qed. 

  Lemma project_until_match (tr: trace St L)
    (trans: St -> L -> St -> Prop) (trans': St' -> L' -> St' -> Prop)
    (VALID: trace_valid trans tr)
    (STEP_KEPT: forall s1 ℓ s2 l, trans s1 ℓ s2 -> proj_lbl ℓ = Some l -> trans' (proj_st s1) l (proj_st s2))
    (PROJ: forall i ℓ, tr L!! i = Some ℓ -> exists l, proj_lbl ℓ = Some l):
    traces_match
      (fun ℓ l => proj_lbl ℓ = Some l) (fun s s' => proj_st s = s')
      trans trans'
      tr (project_trace_until tr).
  Proof.
    generalize dependent tr. cofix IH.
    intros. 
    rewrite (trace_unfold_fold (project_trace_until tr)).
    destruct tr.
    { econstructor. done. }
    apply trace_valid_cons_inv in VALID as [VALID' STEP]. 
    pose proof (PROJ 0 ℓ ltac:(done)) as [l LBL].
    simpl. rewrite LBL. 
    econstructor; try done.
    { rewrite project_until_trfirst. eapply STEP_KEPT; eauto. }
    eapply IH; eauto.
    intros. by apply (PROJ (S i)).
  Qed. 

End TraceProjection.

Section ExtTerm.
  Context `{EM: ExtModel M}. 

  (* TODO: move *)
  Lemma terminating_trace_after {St L: Type} (tr atr: trace St L) i
    (AFTER: after i tr = Some atr)
    (FIN_ATR: terminating_trace atr):
    terminating_trace tr.
  Proof.
    destruct FIN_ATR as [n FIN].
    exists (i + n). by rewrite after_sum' AFTER.
  Qed. 

  Definition ext_trans_bounded (emtr: emtrace) :=
    trans_bounded emtr (fun oℓ => exists ι, oℓ = Some (inr ι)). 
 
  Lemma fin_ext_fair_termination (emtr : emtrace)
    (VALID: emtrace_valid emtr)
    (EXT_BOUND: ext_trans_bounded emtr)
    (FAIR: inner_fair_ext_model_trace emtr)
    (FAIR_TERM_INNER: forall mtr, @mtrace_fairly_terminating M mtr):
    terminating_trace emtr.
  Proof.
    do 2 red in EXT_BOUND. destruct EXT_BOUND as [n BOUND].
    destruct (after n emtr) as [atr| ] eqn:AFTER.
    2: { by exists n. }
    eapply terminating_trace_after; eauto.
    eapply trace_valid_after in VALID; eauto.
    (* set (proj_ext := fun oℓ =>  *)
    unshelve eapply project_until_match in VALID.
    5: exact (fmtrans M). 
    { exact (fun oer => match oer with | Some (inl g) => Some $ Some g | _ => None end). }
    { exact id. }
    2: { simpl. intros. destruct ℓ; simpl in *; try done.
         destruct e; try done. 
         inversion H0. subst. inversion H. congruence. }
    2: { intros. erewrite label_lookup_after in H; eauto.
         apply BOUND in H; [| lia].
         assert (ℓ ≠ None).
         { (* exploit emtr validity.
              Generalize trace_helpers.mtrace_valid_steps'' for that
            *)
           admit. }
         destruct ℓ; [| congruence].
         destruct e; eauto.
         edestruct H; eauto. }
    remember (project_trace_until _ _ _) as mtr. clear Heqmtr. 
    eapply traces_match_preserves_termination; eauto.
    apply FAIR_TERM_INNER.
    { eapply traces_match_valid2; eauto. }
    intros. do 2 red. intros k ENk. 
    specialize (FAIR (inl ρ)). simpl in FAIR. specialize (FAIR ltac:(eauto)).
    do 2 red in FAIR. specialize (FAIR (n + k)). destruct FAIR.
    { apply pred_at_trace_lookup. apply pred_at_trace_lookup in ENk as (?&KTH&?).
      eexists. split.
      { eapply traces_match_state_lookup_2 in KTH as (?&?&?); [| by eauto].
        simpl in *. subst. 
        erewrite <- state_lookup_after; eauto. }
      red. simpl. rewrite /ext_live_roles. set_solver. }
    exists x. apply pred_at_trace_lookup. apply pred_at_trace_lookup in H as (?&NEXT&STEP).
    eexists. split.
    { rewrite -Nat.add_assoc in NEXT. 
      erewrite <- state_lookup_after in NEXT; eauto. 
      eapply traces_match_state_lookup_1 in NEXT as (?&?&?); [| by eauto].
      simpl in *. subst. by rewrite H. }
    red in STEP. destruct STEP as [DIS | STEP].
    { left. intros ?. apply DIS.
      red. simpl. rewrite /ext_live_roles. set_solver. }
    right.
    foobar. 
    
    
    
         
    

End ExtTerm.

(* TODO: move? *)
Section ELM_ALM.
  Context `{LM: LiveModel G M LSI}.
  Context {EM: ExtModel M}.
  Context {LF: LMFairPre LM}.
  Context {ELM: ExtModel LM_Fair}. 

  Definition elmftrace := mtrace (@ext_model_FM _ ELM). 

  Hypothesis (EXT_KEEP_ASG: forall δ1 ι δ2 ρ τ f,
                 @ext_trans _ ELM δ1 (Some $ inr ι) δ2 -> 
                 ls_mapping δ1 !! ρ = Some τ ->
                 ls_fuel δ1 !! ρ = Some f ->
                 ls_mapping δ2 !! ρ = Some τ /\ ls_fuel δ2 !! ρ = Some f). 

  Instance ELM_ALM: AlmostLM (@ext_trans _ ELM) (LM := LM).
  Proof.
    refine {| am_lift_G := Some ∘ inl |}; eauto.
    - intros ??? STEP. inversion STEP. eauto. 
    - intros ?????? STEP NEQ **. inversion STEP; subst. 
      + by destruct (NEQ ρ0).
      + eapply EXT_KEEP_ASG; eauto. 
    - intros [[?|?]| ].
      2, 3: right; by intros [? [=]].
      left; eauto.
  Defined.

  Local Lemma same_type (l: elmftrace) (a: @atrace _ _ _ LM (option ext_role)): False.
  Proof.
    assert (l = a). 
  Abort. 

End ELM_ALM.
