From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import locales_helpers inftraces fairness.
From trillium.fairness.lawyer.obligations Require Import obligations_model.


Section Preservation.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Context `{Countable Locale}. 
  Let OM := ObligationsModel OP. 

  Context {So Lo: Type}.
  Context `{EqDecision Lo}. 
    
  Let out_trace := trace So (Lo).   
  Context (out_step: So -> Lo -> So -> Prop).

  Context (lift_locale: Locale -> Lo).
  Context (out_lbl_prop: Lo -> So -> Prop).
  Hypothesis (LIFT_INJ: Inj eq eq lift_locale). 

  Definition om_live_tids (c: So) (δ: mstate OM) :=
    forall ζ, has_obls OP ζ δ -> out_lbl_prop (lift_locale ζ) c.

  Definition out_om_traces_match: out_trace -> obls_trace OP -> Prop :=
    traces_match
      (fun oℓ τ => oℓ = lift_locale τ)
      om_live_tids
      out_step
      (@mtrans OM).

  Definition out_fair := fair_by out_lbl_prop eq. 

  Lemma out_om_fairness_preserved_single (extr: out_trace) (omtr: obls_trace OP) 
    (τ: Locale):
    out_om_traces_match extr omtr ->
    out_fair (lift_locale τ) extr -> obls_trace_fair OP τ omtr.
  Proof using LIFT_INJ. 
    intros MATCH FAIR. red.
    apply fair_by_equiv. red. intros n OBS.
    destruct (omtr S!! n) as [δ| ] eqn:NTH'; rewrite NTH' in OBS; [| done].
    simpl in OBS. red in OBS. rename OBS into X. 
    destruct (ps_obls OP δ !! τ) as [R| ] eqn:OBS; [| done].
    simpl in X.
    generalize (traces_match_state_lookup_2 _ _ _ _ MATCH NTH').
    intros (c & NTH & LIVE). red in LIVE.
    specialize (LIVE τ ltac:(red; rewrite OBS; done)).
    red in FAIR. apply fair_by_equiv in FAIR. red in FAIR.
    specialize (FAIR n ltac:(rewrite NTH; done)).
    destruct FAIR as (m & c' & MTH & STEP).
    generalize (traces_match_state_lookup_1 _ _ _ _ MATCH MTH).
    intros (δ' & MTH' & LIVE').
    do 2 eexists. split; eauto.
    red. rewrite /has_obls.
    destruct (ps_obls OP δ' !! τ) as [R'| ] eqn:OBS'; [| tauto].
    simpl. destruct (decide (R' = ∅)); [tauto| ].
    right. red in LIVE'. specialize (LIVE' τ ltac:(red; rewrite OBS'; done)).
    red in STEP. destruct STEP as [| (?&STEP& EQ)]; [done| ].
    subst x. 
    generalize (traces_match_label_lookup_1 _ _ _ _ MATCH STEP).
    clear -LIFT_INJ. intros (?&?&?%LIFT_INJ). eauto. 
  Qed.

  Lemma out_om_fairness_preserved (extr: out_trace) (omtr: obls_trace OP):
    out_om_traces_match extr omtr ->
    (forall ζ, out_fair ζ extr) -> (∀ τ, obls_trace_fair OP τ omtr).
  Proof using LIFT_INJ.
    intros MATCH FAIR. intros. eapply out_om_fairness_preserved_single; eauto. 
  Qed. 

End Preservation.
