From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From trillium.traces Require Export traces_match trace_utils exec_traces.
From trillium.program_logic Require Export weakestpre adequacy simulation_adequacy_em.
From fairness Require Export fairness.
From heap_lang Require Export heap_lang_defs lang.


(* TODO: move *)
Definition heap_lang_extrace : Type := extrace heap_lang.


(* TODO: move? *)
Lemma hl_config_wp `{irisG heap_lang M Σ}: ⊢ config_wp.
Proof using.
  rewrite /config_wp. iIntros "!> **".
  done.
Qed.


Section adequacy.

  (* TODO: remove? *)
  Theorem strong_simulation_adequacy_traces_multiple_HL Σ
    `{hPre: @heapGpreS Σ M EM} (s: stuckness) f
    (es: list expr) σ1 (s1: M)
    (R: execution_trace heap_lang → auxiliary_trace M → Prop)
    (p: em_init_param)
    (extr : heap_lang_extrace)
    (Hvex : extrace_valid extr)
    (Hexfirst : trfirst extr = (es, σ1))

    (valid_step: cfg heap_lang -> olocale heap_lang → cfg heap_lang → 
                 mstate M → mlabel M → mstate M -> Prop)
    (state_rel: cfg heap_lang -> mstate M -> Prop)
    (lbl_rel: olocale heap_lang -> mlabel M -> Prop)
    (STEP_LBL_REL: forall c1 oζ c2 δ1 ℓ δ2,
                 valid_step c1 oζ c2 δ1 ℓ δ2 ->
                 lbl_rel oζ ℓ)
    (STEP_MTRANS: forall c1 oζ c2 δ1 ℓ δ2,
                 valid_step c1 oζ c2 δ1 ℓ δ2 ->
                 mtrans δ1 ℓ δ2)
    (R_ST: forall extr mtr, R extr mtr -> state_rel (trace_last extr) (trace_last mtr))
    (R_STEP: forall extr mtr, R extr mtr -> valid_state_evolution_fairness valid_step extr mtr)

    :
    length es ≥ 1 ->
    rel_finitary R →
    em_is_init_st (es, σ1) s1 ->
    (wp_premise_multiple R Σ s f es σ1 s1 p) ->
    ∃ (mtr : trace (mstate M) (mlabel M)), 
      traces_match lbl_rel state_rel locale_step (@mtrans M) extr mtr /\
      trfirst mtr = s1. 
  Proof using.
    intros. eapply strong_simulation_adequacy_traces_multiple; eauto.
    esplit; try by (apply _ || apply hPre). 
  Qed.

  (* TODO: remove? *)
  Theorem strong_simulation_adequacy_traces_HL Σ
    `{hPre: @heapGpreS Σ M EM} (s: stuckness) f
    (e1 : expr) σ1 (s1: M)
    (R: execution_trace heap_lang → auxiliary_trace M → Prop)
    (p: em_init_param)

    (extr : heap_lang_extrace)
    (Hvex : extrace_valid extr)
    (Hexfirst : trfirst extr = ([e1], σ1))

    (valid_step: cfg heap_lang -> olocale heap_lang → cfg heap_lang →
                 mstate M → mlabel M → mstate M -> Prop)
    (state_rel: cfg heap_lang -> mstate M -> Prop)
    (lbl_rel: olocale heap_lang -> mlabel M -> Prop)
    (STEP_LBL_REL: forall c1 oζ c2 δ1 ℓ δ2,
                 valid_step c1 oζ c2 δ1 ℓ δ2 ->
                 lbl_rel oζ ℓ)
    (STEP_MTRANS: forall c1 oζ c2 δ1 ℓ δ2,
                 valid_step c1 oζ c2 δ1 ℓ δ2 ->
                 mtrans δ1 ℓ δ2)
    (R_ST: forall extr mtr, R extr mtr -> state_rel (trace_last extr) (trace_last mtr))
    (R_STEP: forall extr mtr, R extr mtr -> valid_state_evolution_fairness valid_step extr mtr)

    :
    rel_finitary R →
    em_is_init_st ([e1], σ1) s1 ->
    (wp_premise R Σ s f e1 σ1 s1 p) ->
    ∃ (mtr : trace (mstate M) (mlabel M)),
      traces_match lbl_rel state_rel locale_step (@mtrans M) extr mtr /\
      trfirst mtr = s1.
  Proof.
    eapply strong_simulation_adequacy_traces; eauto.
    esplit; try by (apply _ || apply hPre).
  Qed.

End adequacy.
