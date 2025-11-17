From iris.proofmode Require Import tactics.
From fairness Require Import locales_helpers utils fairness.
From lawyer.nonblocking Require Import trace_context calls.
From lawyer.nonblocking.logrel Require Import valid_client.
From heap_lang Require Import lang notation.
From trillium.traces Require Import exec_traces trace_lookup inftraces.

Close Scope Z.

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

  Lemma no_return_before_equiv_nvals tr tpc c i k
    (VALID: extrace_valid tr)
    (ITH: tr S!! i = Some c)
    (NVAL: nval_at tpc c)                                     
    :
    no_return_before tr tpc i k <->
    forall j, i <= j <= k -> from_option (nval_at tpc) True (tr S!! j). 
  Proof using.
    rewrite /no_return_before.
    split.
    - intros NORET j DOM.
      destruct (tr S!! j) as [c'| ] eqn:JTH; [| done]. simpl.
      destruct (decide (nval_at tpc c')); [done| ]. exfalso.
      eapply (call_returns_if_not_continues _ i j) in n; eauto.
      2: lia.
      destruct NORET. destruct n as (r&?&?&?&?&?).
      exists r. split; [lia| ].
      red. do 2 eexists. split; eauto. lia.
    - rewrite /has_return_at. 
      intros CONT (j & LE & (r & c' & GE & JTH & RET)).
      specialize (CONT j ltac:(lia)). rewrite JTH /= in CONT.
      edestruct not_return_nval; eauto.
  Qed.

End CallInTrace.
