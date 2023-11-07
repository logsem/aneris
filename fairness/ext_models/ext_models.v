From trillium.fairness Require Import fairness fair_termination.
From trillium.fairness.examples.ticketlock Require Import set_map_properties. 
From trillium.fairness Require Import trace_helpers lm_fairness_preservation lm_fair fuel.

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
