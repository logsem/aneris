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

  (* TODO: move *)
  Lemma fill_item_nval_strong e1 e2 i1 i2
    (NVAL1: to_val e1 = None) (NVAL2: to_val e2 = None)
    (EQ: fill_item i1 e1 = fill_item i2 e2):
    i1 = i2 /\ e1 = e2. 
  Proof using.
    Set Printing Coercions.
    destruct i1, i2; simpl in EQ.
    all: try congruence.
    all: try by (inversion EQ; subst; done).
  Qed.

  (* TODO: find existing / duplicates? *)
  Lemma fill_item_not_val i e
    (NVAL: to_val e = None):
    to_val (fill_item i e) = None.
  Proof using.
    destruct (to_val (fill_item _ _)) eqn:V; [| done].
    apply mk_is_Some, fill_item_val in V.
    destruct V. set_solver.
  Qed.

  (* (* TODO: move, find existing? *) *)
  (* Lemma fill_item_not_eq i e: *)
  (*   fill_item i e ≠ e. *)
  (* Proof using. *)

  Fixpoint expr_depth (e: expr) :=
    match e with
    | Val _ | Var _ | ChooseNat => 0
    | Rec _ _ e | UnOp _ e | Fst e | Snd e | InjL e
    | InjR e | Fork e | Free e | Load e
                                 => S $ expr_depth e
    | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2
    | AllocN e1 e2 | Store e1 e2 | FAA e1 e2
                                   => S $ max (expr_depth e1) (expr_depth e2)
    | If e0 e1 e2 | Case e0 e1 e2 | CmpXchg e0 e1 e2
                                    => S $ max_list [expr_depth e0; expr_depth e1; expr_depth e2]
      end.

  Lemma fill_item_depth i e:
    expr_depth e < expr_depth (fill_item i e). 
  Proof using.
    destruct i; simpl; lia.
  Qed.

  From lawyer.nonblocking.logrel Require Import substitutions.

  (* TODO: move, find existing? *)
  Lemma fill_app K1 K2 (e: expr):
    fill K1 (fill K2 e) = fill (K2 ++ K1) e. 
  Proof using.
    rewrite /fill. by rewrite foldl_app.
  Qed.

  (* TODO: move, find existing? *)
  Lemma fill_item_fill_1 i (e: expr):
    fill_item i e = fill [i] e. 
  Proof using. done. Qed.

  Lemma fill_item_fill K i e:
    let K' := take (length K) (i :: K) in
    fill K (fill_item i e) = fill_item (default i (last K)) (fill K' e).
  Proof using.
    simpl. 
    rewrite !fill_item_fill_1.
    rewrite !fill_app.
    f_equal.
    simpl. 

    generalize dependent i. clear e. pattern K. apply rev_ind; clear K. 
    { done. }
    intros. simpl. 
    (* we really only need the tail element, IH doesn't matter *)
    clear H. 
    rewrite length_app. simpl.
    rewrite app_comm_cons.
    rewrite take_app_length'.
    2: simpl; lia.
    rewrite last_snoc. done.
  Qed.

  Lemma fill_depth' K e
    (NEMP: K ≠ ectx_emp):
    expr_depth e < expr_depth (fill K e).
  Proof using.
    generalize dependent e.
    revert NEMP. pattern K. apply rev_ind; clear K. 
    { done. }
    simpl. intros.
    destruct l.
    { simpl. apply fill_item_depth. }
    etrans; [apply H; done| ]. 
    rewrite -fill_app. rewrite -fill_item_fill_1. 
    apply fill_item_depth.
  Qed.   

  Lemma fill_depth K e:
    expr_depth e <= expr_depth (fill K e).
  Proof using.
    destruct K.
    { done. }
    apply Nat.lt_le_incl.
    by apply fill_depth'. 
  Qed.

  Lemma fill_eq_inv (e: expr) K
    (EQ: fill K e = e):
    K = [].
  Proof using. 
    destruct K; [done| ].
    symmetry in EQ. 
    apply (@f_equal _ _ expr_depth) in EQ.
    apply Nat.lt_neq in EQ; [done| ].
    by apply fill_depth'.
  Qed.

  (* TODO: move *)
  Lemma ectx_fill_ctx_nval e
    (NVAL: to_val e = None):
    Inj eq eq (flip fill e).
  Proof using.
    red. simpl. intros x. generalize dependent e.
    pattern x. apply rev_ind; clear x; simpl. 
    { intros. symmetry. by eapply fill_eq_inv. } 
    intros a x IH e NVAL y EQ.

    revert EQ. pattern y. apply rev_ind; clear y. 
    { intros EQ. simpl in EQ. by eapply fill_eq_inv. } 

    intros y' b _ EQ.
    rewrite -!fill_app -!fill_item_fill_1 in EQ.
    apply fill_item_nval_strong in EQ as [??].
    2, 3: by apply fill_not_val. 
    subst. f_equal. eauto.
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
