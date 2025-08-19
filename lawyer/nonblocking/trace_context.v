From trillium.traces Require Import exec_traces trace_lookup. 
From trillium.program_logic Require Import language adequacy.


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
