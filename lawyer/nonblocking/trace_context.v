From trillium.traces Require Import exec_traces trace_lookup. 
From trillium.program_logic Require Import language adequacy.
From fairness Require Import locales_helpers utils. 


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

  Lemma not_return_nval tpc c r
    (RET: return_at tpc c r)
    (NVAL: nval_at tpc c):
    False.
  Proof using.
    red in RET, NVAL. unfold expr_at in RET, NVAL. destruct tpc.
    rewrite RET in NVAL.  
    destruct NVAL as (? & EQ & NVAL).
    apply Some_inj, ectx_fill_inj in EQ.
    rewrite -EQ in NVAL. by rewrite to_of_val in NVAL.  
  Qed.

  Lemma call_nval_at {APP} tpc c m a
    (APP_NVAL: forall e1 e2, to_val (APP e1 e2) = None)
    (CALL: call_at tpc c m a (APP := APP)):
  nval_at tpc c.
  Proof using.
    red. eexists. split; eauto.
  Qed.

  Lemma no_expr_in_empty_pool κ σ e:
    ¬ expr_at κ ([], σ) e.
  Proof using. destruct κ. rewrite /expr_at. set_solver. Qed. 

  (* TODO: use in more places *)
  Lemma nval_enabled K τ c
    (NVAL: nval_at (TpoolCtx K τ) c):
    locale_enabled τ c.
  Proof using. 
    red. red in NVAL. simpl in NVAL. destruct NVAL as (?&?&?).
    eexists. split; eauto.
    eapply fill_not_val; eauto.
  Qed.

End ThreadPoolContext.

Section StuckTid.
  Context `{EqDecision (locale Λ)}.

(* TODO: move all of this *)
  Definition not_stuck_tid (τ: locale Λ) (c: cfg Λ) :=
    exists e, from_locale c.1 τ = Some e /\ not_stuck e c.2.

  Definition stuck_tid τ c :=
    exists e, from_locale c.1 τ = Some e /\ stuck e c.2.

  Lemma stuck_tid_neg τ c:
    ¬ not_stuck_tid τ c /\ is_Some (from_locale c.1 τ) <-> stuck_tid τ c.
  Proof using.
    rewrite /not_stuck_tid /stuck_tid.
    setoid_rewrite <- not_not_stuck. 
    split.
    - intros (?&(?&?)). eexists. split; eauto.  
    - intros (?&?&?). split; eauto.
      intros (?&?&?). edestruct H0; eauto. congruence.   
  Qed.
    
  (* TODO: should be provable for heap_lang *)
  Global Instance not_stuck_dec e (c: language.state Λ): Decision (not_stuck e c).
  Proof using.
    rewrite /not_stuck.
    apply or_dec; try solve_decision.
    rewrite /reducible.
  Abort. 

  (* Global Instance not_stuck_tid_dec `{EqDecision (expr Λ)} τ c: Decision (not_stuck_tid τ c). *)
  (* Proof using. *)
  (*   rewrite /not_stuck_tid. *)
  (*   destruct (from_locale c.1 τ) as [e| ] eqn:TT. *)
  (*   2: right; by intros (?&?&?). *)
  (*   destruct (decide (not_stuck e c.2)). *)
  (*   - left. eauto. *)
  (*   - right; intros (?&?&?). congruence. *)
  (* Qed. *)

End StuckTid.


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
