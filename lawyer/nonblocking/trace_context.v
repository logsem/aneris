From trillium.traces Require Import exec_traces trace_lookup. 
From trillium.program_logic Require Import language adequacy.
From fairness Require Import locales_helpers. 


Section ThreadPoolContext.
  Context {Λ: language}. 
  Context `{EqDecision (locale Λ)}. 

  Record tpool_ctx := TpoolCtx {
    tpctx_ctx: ectx Λ;
    tpctx_tid: locale Λ
  }.

  Definition expr_at '(TpoolCtx K τ) (c: cfg Λ) (e: expr Λ) :=
    from_locale c.1 τ = Some (ectx_fill K e).

  Definition call_at {APP: expr Λ -> expr Λ -> expr Λ} tpc c (m a: val Λ) :=
    expr_at tpc c (APP (language.of_val m) (language.of_val a)).

  Definition return_at tpc c (r: val Λ) :=
    expr_at tpc c (language.of_val r).

  Definition nval_at tpc c :=
    exists e, expr_at tpc c e /\ language.to_val e = None.

  Lemma expr_at_in_locales {CNT: Countable (locale Λ)} tc c e
    (EXPR: expr_at tc c e):
    tpctx_tid tc ∈ locales_of_cfg c.
  Proof using.
    red in EXPR. destruct tc, c. simpl in *.
    eapply locales_of_cfg_Some; eauto.
  Qed.

  Global Instance expr_at_dec `{EqDecision (expr Λ)}:
    forall tc c e, Decision (expr_at tc c e).
  Proof using.
    intros [K τ] ??. rewrite /expr_at. 
    destruct (from_locale c.1 τ) as [eτ| ]; solve_decision.  
  Qed.

End ThreadPoolContext.


Section TraceContext.
  Context `{EqDecision (locale Λ)}.

  (* Record trace_ctx := TraceCtx { *)
  (*   tctx_index: nat; *)
  (*   tctx_tid: locale Λ; *)
  (*   tctx_ctx: ectx Λ; *)
  (* }. *)
  Record trace_ctx := TraceCtx {
    tctx_index: nat;
    tctx_tpctx: @tpool_ctx Λ;
  }.
  
  Context (tr: extrace Λ). 

  (* Definition expr_under '(TraceCtx i τ K) (e: expr Λ) := *)
  (*   exists c, tr S!! i = Some c /\ from_locale c.1 τ = Some (ectx_fill K e). *)

End TraceContext.
