From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import locales_helpers comp_utils fairness.
From trillium.fairness.heap_lang Require Import simulation_adequacy notation.
From trillium.fairness.lawyer Require Import counter_model sub_action_em action_model.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_am obligations_em obligations_resources obls_fairness_preservation obls_refill_em obls_refill_model.
From trillium.fairness.lawyer.counter Require Import counter_em.
(* TODO: avoid importing  the other definition*)
From trillium.fairness Require Import trace_lookup.

Definition eo_prog: val.
Admitted. 

Definition eo_ex_dom (l: loc) (extr : heap_lang_extrace) :=
  ∀ (i: nat), ∃ n c, extr S!! n = Some c /\ heap (c.2) !! l = Some #i. 

Definition eo_ex_mono (l: loc) (extr : heap_lang_extrace) :=
  ∀ n c c' oτ (NTH: extr !! n = Some (c, Some (oτ, c'))),
  exists (i j: nat),
    heap c.2 !! l = Some #i /\
    heap c'.2 !! l = Some #j /\
    i <= j
.

Definition eo_ex_progress l extr :=
  (∀ tid, fair_ex tid extr) -> eo_ex_dom l extr /\ eo_ex_mono l extr.

Section EOAdequacy.

  Context {DegO LevelO: ofe}.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO} `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}.
  Context {LIM_STEPS: nat}.

  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.
  
  Context (OP: ObligationsParams Degree Level (locale heap_lang) LIM_STEPS).
  Let ASEMo := ObligationsASEM OP.
  Let ASEMc := @CounterASEM heap_lang.

  (* TODO: move *)
  Instance is_act_of_obls_dec: forall a, Decision (is_action_of (ObligationsRefillAM OP) a).
  Proof. Admitted. 
  Instance is_act_of_cnt_dec: forall a, Decision (is_action_of CounterAM a).
  Proof. Admitted. 

  Let ASEM := ProdASEM (ASEM1 := ASEMo) (ASEM2 := ASEMc).
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} τ => obls OP τ ∅ (H3 := aGS.1)).
  Let PM := ProdAM (ObligationsRefillAM OP) CounterAM.
  Let M := AM2M PM.
  
  Definition eoΣ: gFunctors.
  Admitted.

  Definition eo_st_rel (l: loc) (c: cfg heap_lang) (δ: mstate M) :=
    om_live_tids OP id locale_enabled c δ.1 /\
    heap c.2 !! l = Some #(δ.2).

  Let eo_lbl_match (oτ: olocale heap_lang) (aρ: mlabel M): Prop :=
        from_option (fun ρ => match ρ with
                           | inl τ' => oτ = Some $ locale_of_orm_lbl OP τ'
                           | inr _ => False
                           end) False aρ.2.
    
  Definition eo_traces_match (l: loc): extrace heap_lang -> trace (mstate M) (mlabel M) -> Prop :=
    traces_match
      eo_lbl_match
      (eo_st_rel l)
      locale_step
      (@mtrans M).

  Lemma eo_matching_traces_dom l extr mtr 
    (VALID: extrace_valid extr)
    (MATCH: eo_traces_match l extr mtr)
    (FAIR: ∀ tid, fair_ex tid extr):
    eo_ex_dom l extr.
  Proof using.
  Admitted. 

  Lemma eo_matching_traces_mono l extr mtr 
    (VALID: extrace_valid extr)
    (MATCH: eo_traces_match l extr mtr):
    eo_ex_mono l extr.
  Proof using.
    red. intros.
    pose proof (traces_match_trace_lookup_general _ _ n MATCH) as REL.
    rewrite NTH in REL.
    destruct (mtr !! n) eqn:NTH'; [| done].
    simpl in REL. destruct p as [δ [[ρ δ']|]]; [| tauto].
    simpl in REL. rewrite /eo_st_rel in REL.
    destruct δ as [? m], δ' as [? m']. 
    simpl in REL. destruct REL as ([? LOC] & LBL & [? LOC']).
    do 2 eexists. repeat split; eauto.

    eapply trace_valid_steps' in NTH'.
    2: { eapply traces_match_valid2; eauto. }

    (* TODO: try to extract lemmas about this PM's steps *)
    simpl in NTH'. inversion NTH'; subst; try lia.
    - inversion STEP2.
    - inversion STEP2. subst. inversion STEP. lia.
    - inversion STEP2.
    - inversion STEP2. subst. inversion STEP. lia. 
  Qed.

  Lemma eo_matching_traces_progress l extr mtr 
    (VALID: extrace_valid extr)
    (MATCH: eo_traces_match l extr mtr):
    eo_ex_progress l extr.
  Proof using.
    red. intros. split; eauto using eo_matching_traces_dom, eo_matching_traces_mono.
  Qed.

  (* Theorem eo_simulation_adequacy Σ *)
  (*       (* `{hPre: !heapGpreS Σ EM} (s: stuckness) *) *)
  (*       (* (e1: expr) σ1 (s1: mstate OM) (* p *) *) *)
  (*       (* (INIT: obls_is_init_st OP ([e1], σ1) s1) *) *)
  (*       (* (extr : heap_lang_extrace) *) *)
  (*       (* (Hexfirst : trfirst extr = ([e1], σ1))    : *) *)
  (*       `{hPre: !heapGpreS Σ EM} (s: stuckness) *)
  (*       (e1: expr) σ1 (s1: mstate M) p *)
  (*       (INIT: em_is_init_st ([e1], σ1) s1 (ExecutionModel := EM)) *)
  (*       (extr : heap_lang_extrace) *)
  (*       (* (Hvex : extrace_valid extr) *) *)
  (*       (Hexfirst : trfirst extr = ([e1], σ1))    : *)
  (*   (* rel_finitary (sim_rel LM) → *) *)
  (*   wp_premise Σ s e1 σ1 s1 eofin_sim_rel (p: @em_init_param _ _ EM) ->  *)
  (*   eo_ex_property l extr.  *)
  (* Proof. *)
  (*   rewrite /extrace_fairly_terminating. *)
  (*   intros (* Hterm Hfb *) Hwp (* VALID *) VALID FAIR. *)

  (*   destruct (om_simulation_adequacy_model_trace *)
  (*               Σ _ e1 _ s1 _ INIT _ VALID Hexfirst Hwp) as (omtr&MATCH&OM0). *)

  (*   eapply eo_matching_traces_progress; eauto.  *)
  (* Qed. *)

  (* Theorem eo_progress *)
  (*   (l: loc) *)
  (*   (extr : heap_lang_extrace) *)
  (*   (Hexfirst : trfirst extr = ([eo_prog #0], {| heap := {[l:=#0]}; used_proph_id := ∅ |})): *)
  (*   (* (∀ tid, fair_ex tid extr) -> terminating_trace extr. *) *)
  (*   eo_ex_progress l extr.  *)
  (* Proof using. *)
  (*   assert (heapGpreS eoΣ EM) as HPreG. *)
  (*   { admit. } *)
    
  (*   set (s1 := init_om_state (EO_OP LIM) (trfirst extr)).  *)
    
  (*   unshelve epose proof (simple_om_simulation_adequacy_terminate (EO_OP LIM) eofinΣ NotStuck *)
  (*                 _ _ _ _ *)
  (*                 _ _ EX0) as FAIR_TERM; eauto. *)
  (*   { exact tt. } *)
  (*   { simpl. subst s1. rewrite EX0. apply init_om_state_init. } *)
    
  (*   apply FAIR_TERM. *)
  (*   red. intros ?. iStartProof. iIntros "[HEAP INIT] !>". *)
  (*   iSplitL. *)
  (*   - admit. *)
  (*   - subst s1. rewrite EX0. iApply om_sim_RAH.  *)
  (* Admitted.  *)

End EOAdequacy.
