Require Import Coq.Program.Wf.
Require Import Relation_Operators.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset gmultiset.
From trillium.fairness Require Import locales_helpers inftraces fairness trace_len my_omega utils_multisets utils_tactics obligations_wf obls_termination.
From trillium.fairness.lawyer.obligations Require Import obligations_model wf_utils wf_ms.
From stdpp Require Import relations.


Section UnfairTermination.
  Context `{OP: ObligationsParams Degree Empty_set Locale LIM_STEPS}.
  Let OM := ObligationsModel.

  Context (tr: obls_trace).
  Hypothesis 
    (VALID: obls_trace_valid tr)
    (TR_WF: ∀ i δ, tr S!! i = Some δ → om_st_wf δ)
    (DEG_WF: wf (strict deg_le))
  .

  Lemma no_obls_wo_lvls δ (WF: om_st_wf δ):
    forall τ, default ∅ (ps_obls δ !! τ) = ∅.
  Proof using.
    clear -WF. 
    intros τ. destruct (ps_obls δ !! τ) as [R| ] eqn:OB; [| done]. simpl.
    destruct (set_choose_or_empty R) as [[s IN]| ]; [| set_solver].
    pose proof (om_wf_obls_are_sigs _ WF s) as SIG.
    rewrite flatten_gset_spec in SIG.
    setoid_rewrite elem_of_map_img in SIG. specialize (SIG ltac:(set_solver)).
    apply elem_of_dom in SIG as [[??] ?]. done.
  Qed.

  Lemma always_fair_wo_lvls:
    forall τ, obls_trace_fair τ tr.
  Proof using TR_WF.
    intros τ. red.
    apply fair_by_equiv. intros n OB.
    destruct (tr S!! n) eqn:NTH; rewrite NTH in OB; [| done]. 
    simpl in OB. red in OB.
    destruct OB. apply no_obls_wo_lvls.
    eapply TR_WF; eauto.
  Qed.

  Lemma always_term_wo_lvls:
    terminating_trace tr. 
  Proof using VALID TR_WF DEG_WF.
    apply obls_fair_trace_terminate; auto.
    2: { done. }
    apply always_fair_wo_lvls. 
  Qed.

End UnfairTermination.
