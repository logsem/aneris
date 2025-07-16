From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From trillium.program_logic Require Import execution_model weakestpre adequacy. 
From fairness Require Import fairness.
From lawyer.examples Require Import orders_lib.
From lawyer.obligations Require Import obligations_resources obligations_model obligations_em.


Section TraceContext.
  Context `{EqDecision (locale Λ)}.

  Record trace_ctx := TraceCtx {
    tctx_index: nat;
    tctx_tid: locale Λ;
    tctx_ctx: ectx Λ;
  }.
  
  Context (tr: extrace Λ). 

  Definition expr_under '(TraceCtx i τ K) (e: expr Λ) :=
    exists c, tr S!! i = Some c /\ from_locale c.1 τ = Some (ectx_fill K e).

End TraceContext.


Section ObligationsWaitFreeEM.
  Context `{Countable (locale Λ)}.

  Context (ic: @trace_ctx Λ). (** location of the infinite call *)
  Context (F: nat). (** amount of fuel required for the call (currently at d0) *)

  Definition WF_SB := 1.

  Instance OP_WF: ObligationsParams (bounded_nat 2) unit (locale Λ) WF_SB.
  esplit; try by apply _.
  - apply nat_bounded_PO.
  - apply unit_PO.
  Defined.

  Let OM := ObligationsModel.
  Notation "'Degree'" := (bounded_nat 2). 
  Notation "'Level'" := (unit).

  Let d0: Degree := ith_bn 2 0 ltac:(lia).
  Let d1: Degree := ith_bn 2 1 ltac:(lia).
  Let l0: Level := tt.

  Definition extra_fuel `{!ObligationsGS Σ} (omtr: auxiliary_trace OM) :=
    let len := trace_length omtr in
    let i := tctx_index ic in
    if i <? len then (cp_mul π0 d0 (len - i) ∗ cp_mul π0 d0 F)%I else ⌜ True ⌝%I.

  Definition cur_phases `{!ObligationsGS Σ} (omtr: auxiliary_trace OM): iProp Σ :=
    let δ := trace_last omtr in
    let τ := tctx_tid ic in
    ([∗ map] τ' ↦ π' ∈ delete τ (ps_phases δ), th_phase_eq τ' π') ∗
    let ph_res π := let q := if (tctx_index ic <? trace_length omtr) 
                             then 1%Qp else (/2)%Qp
                    in th_phase_frag τ π q in
    from_option ph_res ⌜ True ⌝%I (ps_phases δ !! τ).

  Definition cur_obls_sigs `{!ObligationsGS Σ} (omtr: auxiliary_trace OM): iProp Σ :=
    let δ := trace_last omtr in
    let τ := tctx_tid ic in
    ([∗ set] τ' ∈ dom (ps_obls δ) ∖ {[ τ ]}, obls τ' ∅) ∗
    if decide (τ ∈ dom (ps_obls δ))
    then (∃ s, obls τ {[ s ]} ∗ sgn s l0 (Some false) ∗ ep s π0 d0)%I
    else cp π0 d1. 

  Definition obls_wfree_ti `{!ObligationsGS Σ}
    (etr: execution_trace Λ) (omtr: auxiliary_trace OM): iProp Σ :=
    obls_ti etr omtr ∗ extra_fuel omtr ∗ cur_phases omtr ∗ cur_obls_sigs omtr.

  foobar. 
  Definition ObligationsEM: ExecutionModel Λ OM :=
    {| 
      em_Σ := obls_Σ;
      em_valid_evolution_step := obls_valid_evolution_step;
      em_thread_post Σ `{!ObligationsGS Σ} :=
        fun τ _ => (obls τ ∅)%I;
      em_initialization := obls_resources_init;
    |}.


End ObligationsWaitFreeEM.
