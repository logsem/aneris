From iris.proofmode Require Import tactics.
From fairness Require Import locales_helpers utils fairness.
From lawyer.nonblocking Require Import trace_context.
From lawyer.nonblocking.logrel Require Import valid_client.
From heap_lang Require Import lang notation.
From trillium.traces Require Import exec_traces trace_lookup inftraces.


Close Scope Z. 


Section UnderCtx.

  Local Definition check P `{Decision P} (e: expr) :=
    if (decide P) then Some e else None. 

  Definition under_ctx_item (Ki: ectx_item) (e: expr): option expr :=
    match Ki, e with 
  | AppLCtx vc2, App e e2 => check (e2 = of_val vc2) e
  | AppRCtx ec1, App e1 e => check (e1 = ec1) e
  | UnOpCtx opc, UnOp op e => check (op = opc) e
  | BinOpLCtx opc vc, BinOp op e1 v2 => check (op = opc /\ v2 = vc) e1
  | BinOpRCtx opc ec, BinOp op e1 e2 => check (op = opc /\ e1 = ec) e2
  | IfCtx ec1 ec2, If e e1 e2 => check (e1 = ec1 /\ e2 = ec2) e
  | PairLCtx vc2, Pair e (Val v2) => check (v2 = vc2) e
  | PairRCtx ec1, Pair e1 e => check (e1 = ec1) e
  | FstCtx, Fst e => Some e
  | SndCtx, Snd e => Some e
  | InjLCtx, InjL e => Some e
  | InjRCtx, InjR e => Some e
  | CaseCtx ec1 ec2, Case e e1 e2 => check (e1 = ec1 /\ e2 = ec2) e
  | AllocNLCtx vc2, AllocN e (Val v2) => check (v2 = vc2) e
  | AllocNRCtx ec1, AllocN e1 e => check (e1 = ec1) e
  | FreeCtx, Free e => Some e
  | LoadCtx, Load e => Some e
  | StoreLCtx vc2, Store e (Val v2) => check (v2 = vc2) e
  | StoreRCtx ec1, Store e1 e => check (e1 = ec1) e
  | CmpXchgLCtx vc1 vc2, CmpXchg e (Val v1) (Val v2) => check (v1 = vc1 /\ v2 = vc2) e
  | CmpXchgMCtx ec0 vc2, CmpXchg e0 e (Val v2) => check (e0 = ec0 /\ v2 = vc2) e
  | CmpXchgRCtx ec0 ec1, CmpXchg e0 e1 e => check (e0 = ec0 /\ e1 = ec1) e
  | FaaLCtx vc2, FAA e (Val v2) => check (v2 = vc2) e
  | FaaRCtx ec1, FAA e1 e => check (e1 = ec1) e
  | _, _ => None
    end.

  Local Lemma not_eq_helper (x e1 e2: expr)
    (NEQ: e1 ≠ e2):
    None = Some x <-> e1 = e2.
  Proof using. trans False; done. Qed.
    
  Lemma under_ctx_item_spec Ki e e':
    under_ctx_item Ki e = Some e' <-> fill_item Ki e' = e.
  Proof using.
    destruct Ki, e; simpl.
    all: try by apply not_eq_helper. 
    Local Ltac solve_iff := rewrite /check; destruct decide; try apply not_eq_helper; subst; set_solver.
    all: try by solve_iff.
    all: try by set_solver.
    all: try by (destruct e2; by apply not_eq_helper || solve_iff). 
    - destruct e2, e3; by apply not_eq_helper || solve_iff.
    - destruct e3; by apply not_eq_helper || solve_iff.
  Qed. 

  Fixpoint under_ctx (K: ectx heap_lang) (e: expr): option expr :=
    match K with
    | [] => Some e
    | Ki :: K' => from_option (under_ctx_item Ki) None (under_ctx K' e)
    end. 

  Lemma under_ctx_spec K e e':
    under_ctx K e = Some e' <-> fill K e' = e.
  Proof using.
    generalize dependent e. generalize dependent e'.
    induction K.
    { simpl. set_solver. }
    intros. simpl. destruct under_ctx eqn:ITEM.
    2: { apply not_eq_helper.
         intros EQ. rewrite -IHK in EQ. congruence. }
    rewrite under_ctx_item_spec.
    apply IHK in ITEM. simpl in *.
    rewrite -ITEM. split.
    + by intros <-.
    + by intros ?%ectx_fill_inj.
  Qed.

  Lemma under_ctx_spec_neg K e:
    under_ctx K e = None <-> forall e', fill K e' ≠ e.
  Proof using.
    simpl. split; intros. 
    - intros EQ%under_ctx_spec. congruence.
    - destruct under_ctx eqn:UC; [| done].
      apply under_ctx_spec in UC.
      edestruct H; eauto.
  Qed.

  Lemma under_ctx_fill K e:
    under_ctx K (fill K e) = Some e.
  Proof using. by apply under_ctx_spec. Qed.

  Lemma under_ctx_val_Some_inv (e ec: expr) K
    (CTX: under_ctx K e = Some ec)
    (VAL: is_Some (language.to_val e)):
    K = ectx_emp /\ ec = e.
  Proof using.
    apply under_ctx_spec in CTX. simpl in *.
    destruct K; simpl in CTX; subst; try done.
    simpl in VAL.
    rewrite fill_not_val in VAL.
    { by destruct VAL. }
    by destruct e0. 
  Qed.

  (** specific to heap_lang, as it requires under_ctx *)
  Global Instance nval_at_dec:
    forall tc c, Decision (nval_at tc c).
  Proof using.
    intros [K τ] ?. rewrite /nval_at /expr_at.
    apply ex_fin_dec with
             (l := from_option
                     (fun e => from_option (flip cons nil) [] (under_ctx K e))
                     [] (from_locale c.1 τ)); [apply _| ].
    intros ec (IN & NVAL).
    rewrite IN. simpl. rewrite under_ctx_fill. simpl. tauto.  
  Qed.

End UnderCtx.


Section FitsInfCall.

  Context (ic: @trace_ctx heap_lang).
  Let ii := tctx_index ic.
  Let tc := tctx_tpctx ic. 
  Let Ki := tpctx_ctx tc.
  Let τi := tpctx_tid tc. 

  Context (m: val) (ai: val). 

  Definition fits_inf_call (etr: execution_trace heap_lang): Prop :=
    from_option (fun c => call_at tc c m ai (APP := App)) True (etr !! ii) /\
    (forall j, ii <= j -> from_option (nval_at tc) True (etr !! j)) /\
    (forall i, from_option (fun e => to_val e = None) True
            (from_option (fun c => from_locale c.1 τi) None (etr !! i))).

  Lemma fits_inf_call_last_or_short etr
    (FITS: fits_inf_call etr):
    (nval_at tc (trace_last etr)) \/ trace_length etr <= ii. 
  Proof using.
    edestruct Nat.lt_ge_cases as [LT| ]; [| by eauto].
    red in FITS. apply proj2, proj1 in FITS. red in LT.
    ospecialize * (FITS (trace_length etr - 1)).
    { lia. }
    rewrite trace_lookup_last in FITS.
    2: { lia. }
    simpl in FITS. by left.
  Qed.

  (* TODO: move *)
  Lemma ft_lookup_old {St L: Type} (tr: finite_trace St L) s l i c
    (ITH: tr !! i = Some c):
    (tr :tr[ l ]: s) !! i = Some c.
  Proof using. 
    rewrite trace_lookup_extend_lt; [done| ]. 
    by apply trace_lookup_lt_Some.
  Qed.

  Lemma fits_inf_call_prev: filter_pref_closed fits_inf_call. 
  Proof using.
    red. intros etr τ c FITS. 
    pose proof (ft_lookup_old etr c τ) as LOOKUP.  
    destruct FITS as (II & FITS & NVAL). split; [| split]. 
    - destruct (etr !! ii) eqn:ITH; [| done].
      simpl. 
      eapply LOOKUP in ITH.
      rewrite ITH in II. eauto.
    - intros ? LE.
      specialize (FITS _ LE).
      destruct (etr !! j) eqn:JTH; [| by eauto]. simpl.
      eapply LOOKUP in JTH.
      by rewrite JTH in FITS.
    - intros.
      destruct (etr !! i) as [c0| ] eqn:ITH; [| done].
      destruct (from_locale c0.1 τi) eqn:TT; simpl.
      2: { by rewrite TT. }  
      specialize (NVAL i). erewrite LOOKUP in NVAL; eauto.
  Qed.

  Lemma runs_call_helper t1 t2 e σ
    (EQ: τi = locale_of t1 e)
    (RUNS: nval_at tc (t1 ++ e :: t2, σ)):
    exists ec, under_ctx Ki e = Some ec /\ to_val ec = None.
  Proof using.
    red in RUNS. destruct tc. simpl in RUNS. 
    pose proof (from_locale_from_Some [] (t1 ++ e :: t2) t1 e) as X.
    ospecialize (X _).
    { apply prefixes_from_spec. eauto. }
    simpl in X. subst τi. simpl in EQ. rewrite EQ /from_locale in RUNS.
    rewrite X in RUNS. destruct RUNS as (?&?&?).
    inversion H. subst. rewrite under_ctx_fill. eauto. 
  Qed.

  Lemma fic_has_τi etr
    (FITS : fits_inf_call etr)
    (LEN: ii < trace_length etr):
    τi ∈ locales_of_cfg (trace_last etr).
  Proof using.
    red in FITS. 
    destruct FITS as (_ & NEXT & _).
    ospecialize (NEXT (trace_length etr - 1) _).
    { lia. }
    rewrite trace_lookup_last in NEXT.
    2: { lia. }
    simpl in NEXT. rewrite /nval_at /expr_at in NEXT.
    destruct NEXT as (?&IN&?).
    eapply locales_of_cfg_Some; eauto.
    destruct tc. eauto.  
    Unshelve. exact inhabitant.
  Qed.

  Global Instance fic_dec: ∀ etr, Decision (fits_inf_call etr).
  Proof using.
    intros. rewrite /fits_inf_call.
    apply and_dec.
    { destruct (etr !! ii); solve_decision. }
    apply and_dec; cycle 1. 
    - apply Decision_iff_impl with
        (P := Forall (fun i => from_option (fun e => to_val e = None) True
                        (from_option (fun c => from_locale c.1 τi) None (etr !! i)))
                (seq 0 (trace_length etr))).
      2: { apply Forall_dec. intros i.
           destruct lookup; try solve_decision. simpl.
           destruct from_locale; solve_decision. }
      rewrite List.Forall_forall.
      simpl.
      apply forall_proper. intros i.
      rewrite in_seq. simpl.
      fold τi. split; auto.
      intros.
      destruct lookup eqn:ITH; try done. simpl in *.
      apply H. split; [lia| ].
      eapply trace_lookup_lt_Some_1; eauto. 
    - apply Decision_iff_impl with (P := Forall (fun j => from_option (nval_at tc) True (etr !! j)) (seq ii (trace_length etr - tctx_index ic))).
      2: { apply Forall_dec. intros. destruct lookup; solve_decision. }
      rewrite List.Forall_forall. simpl.
      apply forall_proper. intros i.
      rewrite in_seq.
      split; intros X II.
      2: { apply X. lia. }
      destruct (etr !! i) eqn:ITH; try done. apply X.
      split; auto.
      apply trace_lookup_lt_Some_1 in ITH. 
      rewrite -Nat.le_add_sub; [done| ]. 
      edestruct Nat.le_gt_cases as [LE | GT]; [by apply LE| ].
      simpl in *. lia. 
  Qed.

End FitsInfCall. 

Section CallInTrace.
  Context (m: val).
  
  Definition has_return_at (tr: extrace heap_lang) '(TraceCtx i tpc as tc) j :=
    exists r cj, i <= j /\ tr S!! j = Some cj /\ return_at tpc cj r.

  Definition has_return tr tc := exists j, has_return_at tr tc j.

  Definition no_return_before tr tpc i k :=
    ¬ (exists j, j <= k /\ has_return_at tr (TraceCtx i tpc) j). 

  Definition fair_call tr '(TpoolCtx K τ as tpc) i :=
    forall k ck, i <= k -> 
            tr S!! k = Some ck ->
            locale_enabled τ ck ->
            (* ¬ (exists j, j <= k /\ has_return_at tr (TraceCtx i tpc) j) -> *)
            no_return_before tr tpc i k ->
    exists d cd, tr S!! (k + d) = Some cd /\
            fairness_sat locale_enabled tid_match τ cd (tr L!! (k + d)). 

  Definition always_returns tr :=    
    forall tc a ci, let '(TraceCtx i tpc) := tc in
      (* fair_ex (tpctx_tid tpc) tr -> *)
      fair_call tr tpc i ->
      tr S!! i = Some ci ->
      call_at tpc ci m a (APP := App) ->
      has_return tr tc.

  (* TODO: generalize to multiple threads *)
  Definition valid_init_tpool (tp: list expr) :=
    (exists e0, tp = [subst "m" m e0] /\ valid_client e0). 
  
  Definition wait_free (is_init_st: cfg heap_lang -> Prop) := forall etr,
      valid_init_tpool (trfirst etr).1 ->
      is_init_st (trfirst etr) ->
      extrace_valid etr ->
      always_returns etr.

End CallInTrace.
