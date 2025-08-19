From iris.proofmode Require Import tactics.
From fairness Require Import locales_helpers.
From lawyer.nonblocking Require Import trace_context.
From heap_lang Require Import lang notation.


Close Scope Z. 


Section UnderCtx.

  (* TODO: move *)
  Definition under_ctx (K: ectx heap_lang) (e: expr): option expr.
  Admitted.

  Lemma under_ctx_spec K e e':
    under_ctx K e = Some e' <-> ectx_fill K e' = e.
  Proof using. Admitted.

  Lemma under_ctx_fill K e:
    under_ctx K (ectx_fill K e) = Some e.
  Proof using. Admitted. 

End UnderCtx.


Section CallInTrace.

  Context (ic: @trace_ctx heap_lang).
  Let ii := tctx_index ic.
  Let Ki := tctx_ctx ic.
  Let τi := tctx_tid ic.

  Definition runs_call (ec: expr) (c: cfg heap_lang): Prop :=
    exists e, from_locale c.1 τi = Some e /\ under_ctx Ki e = Some ec /\ to_val ec = None.

  Context (m: val) (ai: val). 

  Definition fits_inf_call (etr: execution_trace heap_lang): Prop :=
    from_option (runs_call (m ai)) True (etr !! ii) /\
    forall j, ii <= j -> from_option (fun c => exists ec, runs_call ec c) True (etr !! j).

  Lemma fits_inf_call_last_or_short etr
    (FITS: fits_inf_call etr):
    (exists ec, runs_call ec (trace_last etr)) \/ trace_length etr <= ii. 
  Proof using.
    edestruct Nat.lt_ge_cases as [LT| ]; [| by eauto].
    red in FITS. apply proj2 in FITS. red in LT.
    ospecialize * (FITS (trace_length etr - 1)).
    { lia. }
    rewrite trace_lookup_last in FITS.
    2: { lia. }
    simpl in FITS. by left.
  Qed.

  Lemma fits_inf_call_prev etr τ c
    (FITS: fits_inf_call (etr :tr[τ]: c)):
    fits_inf_call etr.
  Proof using.
    assert (forall j cj, etr !! j = Some cj -> (etr :tr[ τ ]: c) !! j = Some cj) as LOOKUP.
    { intros. simpl.
      rewrite trace_lookup_extend_lt; [done| ]. 
      by apply trace_lookup_lt_Some. }
    red.
    destruct FITS as [II FITS]. split.
    { destruct (etr !! ii) eqn:ITH; rewrite ITH; [| done].
      apply LOOKUP in ITH.
      by rewrite ITH in II. }
    intros ? LE.
    specialize (FITS _ LE).
    destruct (etr !! j) eqn:JTH; rewrite JTH; [| by eauto]. simpl.
    apply LOOKUP in JTH.
    by rewrite JTH in FITS. 
  Qed.

  Lemma runs_call_helper t1 t2 e ec σ
    (EQ: τi = locale_of t1 e)
    (RUNS: runs_call ec (t1 ++ e :: t2, σ)):
    under_ctx Ki e = Some ec /\ to_val ec = None.
  Proof using.
    red in RUNS. destruct RUNS as (e_ & TIth & CUR & NVAL).
    simpl in TIth.
    pose proof (from_locale_from_Some [] (t1 ++ e :: t2) t1 e) as X.
    ospecialize (X _).
    { apply prefixes_from_spec. eauto. }
    simpl in X. rewrite EQ /from_locale in TIth. 
    rewrite TIth in X. inversion X. subst. eauto.
  Qed.

  Lemma fic_has_τi etr
    (FITS : fits_inf_call etr)
    (LEN: ii < trace_length etr):
    τi ∈ locales_of_cfg (trace_last etr).
  Proof using.
    red in FITS. 
    destruct FITS as [_ NEXT].
    ospecialize (NEXT (trace_length etr - 1) _).
    { lia. }
    rewrite trace_lookup_last in NEXT.
    2: { lia. }
    simpl in NEXT. rewrite /runs_call in NEXT.
    destruct NEXT as (?&?&IN&?).
    eapply locales_of_cfg_Some; eauto.
    Unshelve. exact inhabitant.
  Qed.

End CallInTrace. 
