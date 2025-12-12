From iris.proofmode Require Import tactics.
From fairness Require Import locales_helpers utils fairness.
From lawyer.nonblocking Require Import trace_context calls.
From lawyer.nonblocking.logrel Require Import valid_client.
From heap_lang Require Import lang notation locales_helpers_hl.
From trillium.traces Require Import exec_traces trace_lookup inftraces.

Close Scope Z.

(* TODO: move all of this *)
  Definition not_stuck_tid τ c :=
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
    
  (* TODO: is it provable for general Λ? *)
  Global Instance not_stuck_dec {Λ} e (c: language.state Λ): Decision (not_stuck e c).
  Proof using.
    rewrite /not_stuck.
    apply or_dec; try solve_decision.
    rewrite /reducible.
  Admitted. 

  Global Instance not_stuck_tid_dec τ c: Decision (not_stuck_tid τ c).
  Proof using.
    rewrite /not_stuck_tid.
    apply ex_fin_dec with (l := c.1).
    { solve_decision. }
    intros ? (?%from_locale_lookup&?).
    apply elem_of_list_In. eapply elem_of_list_lookup; eauto.
  Qed.


Section CallInTrace.
  Context (m: val).
  
  Definition has_return_at (tr: extrace heap_lang) '(TraceCtx i tpc as tc) j :=
    exists r cj, i <= j /\ tr S!! j = Some cj /\ return_at tpc cj r.

  Definition has_return tr tc := exists j, has_return_at tr tc j.

  Definition gets_stuck_at (tr: extrace heap_lang) '(TraceCtx i (TpoolCtx _ τ)) j :=
    exists cj, i <= j /\ tr S!! j = Some cj /\ stuck_tid τ cj.

  (* Definition gets_stuck tr tc := exists j, gets_stuck_at tr tc j. *)
  (* TODO: write a comment *)
  (* so far this stronger condition is necessary to prove main call reduction *)
  Definition gets_stuck_ae tr tc :=
    forall N, is_Some (tr S!! N) -> exists j, j >= N /\ is_Some (tr S!! j) /\ gets_stuck_at tr tc j.

  Definition no_return_before tr tpc i k :=
    ¬ (exists j, j <= k /\ has_return_at tr (TraceCtx i tpc) j). 

  Definition locale_enabled_safe τ c :=
    locale_enabled τ c /\ not_stuck_tid τ c. 

  (** see fair_call_strenghten for an equivalent definition used in paper *)
  Definition fair_call tr '(TpoolCtx K τ as tpc) i :=
    forall k ck, i <= k -> 
            tr S!! k = Some ck ->
            locale_enabled_safe τ ck ->
            (* ¬ (exists j, j <= k /\ has_return_at tr (TraceCtx i tpc) j) -> *)
            no_return_before tr tpc i k ->
    exists d cd, tr S!! (k + d) = Some cd /\
            fairness_sat locale_enabled_safe tid_match τ cd (tr L!! (k + d)). 

  (* TODO: rename *)
  Definition always_returns (s: stuckness) tr :=    
    forall tc a ci, let '(TraceCtx i tpc) := tc in
      (* fair_ex (tpctx_tid tpc) tr -> *)
      fair_call tr tpc i ->
      tr S!! i = Some ci ->
      call_at tpc ci m a (APP := App) ->
      has_return tr tc \/ s = MaybeStuck /\ gets_stuck_ae tr tc. 

  Definition valid_op_client e := exists e0, e = subst "m" m e0 /\ valid_client e0.

  Definition valid_init_tpool (tp: list expr) := Forall valid_op_client tp. 
  
  Definition wait_free (is_init_st: cfg heap_lang -> Prop) (s: stuckness) := forall etr,
      valid_init_tpool (trfirst etr).1 ->
      is_init_st (trfirst etr) ->
      extrace_valid etr ->
      always_returns s etr.

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

  Lemma no_return_before_neg_equiv_ret tr tpc c i k
    (VALID: extrace_valid tr)
    (ITH: tr S!! i = Some c)
    (NVAL: nval_at tpc c)                                     
    :
    ¬ no_return_before tr tpc i k <->
    exists j, i <= j <= k /\ from_option (fun c => exists a, return_at tpc c a) False (tr S!! j). 
  Proof using.
    rewrite no_return_before_equiv_nvals; eauto.
    split.
    - intros NORET. apply not_forall_exists_not in NORET as (j & [XX YY]%Classical_Prop.imply_to_and).
      destruct (tr S!! j) eqn:JTH; [| done]; simpl in *.
      eapply (call_returns_if_not_continues _ i j) in YY; eauto.
      2: lia.
      destruct YY as (r&?&?&?&?&?).
      exists r. split; [lia| ].
      rewrite H0 /=. eauto.
    - intros (j & DOM & RET).
      destruct (tr S!! j) eqn:JTH; [| done].
      simpl in RET.
      intros CONT. specialize (CONT j ltac:(lia)).
      rewrite JTH /= in CONT.
      destruct RET.
      eapply not_return_nval; eauto.
  Qed.

  (* TODO: move, use in other places *)
  Lemma nval_enabled K τ c
    (NVAL: nval_at (TpoolCtx K τ) c):
  locale_enabled τ c.
  Proof using. 
    red. red in NVAL. simpl in NVAL. destruct NVAL as (?&?&?).
    eexists. split; eauto.
    eapply fill_not_val; eauto.
  Qed.

  (** definition used in paper *)  
  Definition fair_call_strong tr '(TpoolCtx K τ as tpc) i :=
    forall k c, i <= k -> tr S!! k = Some c ->
           no_return_before tr tpc i k ->           
    exists d, tr L!! (k + d) = Some $ Some τ \/
         (** Note that we allow τ to be not stuck at k and stuck at (k+d).
             There are programs where a thread gets (un)stuck due to other threads' actions, i.e. trying to read a location being deallocated concurrently.
             In fact, we exclude such programs (to prove logical relation).
             But we do not exploit the resulting "being stuck is a thread-local property". *)
         from_option (stuck_tid τ) False (tr S!! (k + d)). 

  Lemma fair_call_strenghten tr K τ i
    (tpc := TpoolCtx K τ)
    (VALID: extrace_valid tr)
    (CALLi: from_option (fun c => exists a, call_at tpc c m a (APP := App)) False (tr S!! i)): 
    fair_call tr (TpoolCtx K τ) i <-> fair_call_strong tr (TpoolCtx K τ) i.
  Proof using.
    rewrite /fair_call /fair_call_strong.
    apply forall_proper. intros k. 
    split.
    2: { intros FAIR ? LE KTH EN NORET.
         destruct (decide (not_stuck_tid τ ck)).
         2: { exists 0. rewrite Nat.add_0_r.
              eexists. split; eauto.
              red. left. intros (?&?). by apply n. } 
         ospecialize * FAIR; eauto.
         destruct FAIR as [d STEP].
         destruct STEP as [STEP | STUCK]. 
         - pose proof STEP as [[??] _]%mk_is_Some%label_lookup_states.
           do 2 eexists. split; eauto.
           red. eauto. right. eexists. by split; eauto.
         - destruct (tr S!! (k + d)) eqn:DTH; [| done]. simpl in STUCK.
           exists d. eexists. split; eauto.
           red. left. intros (?&NS).
           apply stuck_tid_neg in STUCK. tauto. }
           
    intros FAIR c LE KTH NORET.
    destruct (tr S!! i) eqn:ITH; [| done]. simpl in CALLi. destruct CALLi.
    destruct (decide (not_stuck_tid τ c)) as [NS | STUCK].
    2: { exists 0. right. rewrite Nat.add_0_r KTH /=.
         apply stuck_tid_neg. split; auto.
         eapply from_locale_trace in LE; eauto.
         by rewrite KTH /= in LE. } 
         
    ospecialize * FAIR; eauto.
    { odestruct (decide (locale_enabled_safe _ _ )) as [EN | DIS]; [by apply EN| ].
      eapply call_returns_if_not_continues in LE; eauto.
      { destruct LE as (?&?&?&?&?&RET).
        edestruct NORET. eexists. split; [apply H0| ].
        red. do 2 eexists. split; eauto. lia. }
      { eapply (@call_nval_at _ _ App); eauto. }
      intros NVAL. apply DIS.
      split; auto. 
      eapply nval_enabled; eauto. }
    rewrite /fairness_sat in FAIR. destruct FAIR as (d&?&?&[DIS | (?&?&STEP)]).
    2: { red in STEP. subst. eauto. }

    rewrite /locale_enabled_safe in DIS.
    apply not_and_r in DIS as [DIS | STUCK].
    2: { eexists. right. erewrite H0. simpl.
         apply stuck_tid_neg. split; auto.
         pose proof KTH as KK. eapply (from_locale_trace _ k) in KK.
         { erewrite H0 in KK. apply KK. }
         { eauto. }
         2: lia.
         destruct NS as (?&?&?). eauto. }
    
    eapply (enabled_disabled_step_between _ k (k + d)) in DIS; eauto.
    2: lia.
    2: { eapply no_return_before_equiv_nvals in NORET; eauto.
         2: { eapply (@call_nval_at _ _ App); eauto. }
         rewrite KTH /= in NORET. eapply nval_enabled; eauto. } 
    destruct DIS as (?&GE&?).
    apply proj1, Nat.le_sum in GE as [? ->].
    eauto.
  Qed.

  Definition always_returns_strong s tr :=
    forall tc a ci, let '(TraceCtx i tpc) := tc in
      fair_call_strong tr tpc i ->
      tr S!! i = Some ci ->
      call_at tpc ci m a (APP := App) ->
      has_return tr tc \/ s = MaybeStuck /\ gets_stuck_ae tr tc. 

  Definition wait_free_strong (is_init_st: cfg heap_lang -> Prop) s := forall etr,
      valid_init_tpool (trfirst etr).1 ->
      is_init_st (trfirst etr) ->
      extrace_valid etr ->
      always_returns_strong s etr.

  Lemma wait_free_equiv C s:
    wait_free C s <-> wait_free_strong C s.
  Proof using.
    rewrite /wait_free /wait_free_strong.
    repeat (apply forall_proper; intros).
    destruct x3 as [? [??]]. 
    split; intros RET **; apply RET; auto.
    all: eapply fair_call_strenghten; eauto;
      rewrite H0; simpl; exists x4; eauto.
  Qed.

End CallInTrace.


Section RestrWFree.

  Definition valid_init_tpool_restr (tp: list expr) (ms: gmap val nat) :=
    (** e.g.: {m1: 2, m2: 1} -> [m1, m1, m2] *)
    let ms' := flat_map (fun '(m, k) => repeat m k) $ map_to_list ms in
    (* TODO: allow "smaller" thread pools too *)
    (* TODO: move "no fork" condition outside? *)
    Forall2 (fun m e => valid_op_client m e /\ no_forks e) ms' tp. 

  (** TODO: account for multiple m's in unrestricted wait-freedom too *)
  Definition wait_free_restr (ms: gmap val nat) (is_init_st: cfg heap_lang -> Prop) s := forall etr,
      valid_init_tpool_restr (trfirst etr).1 ms ->
      is_init_st (trfirst etr) ->
      extrace_valid etr ->
      forall m, m ∈ dom ms -> always_returns m s etr.  

End RestrWFree.


Section FitsInfCall.

  (* TODO: do we need a similar def for infinite traces? *)
  Definition previous_calls_return (etr: execution_trace heap_lang) i τ m :=
    forall j K, let tpc := TpoolCtx K τ in
           j < i ->
           from_option (fun c => exists a, call_at tpc c m a (APP := App)) False (etr !! j) ->
           exists r, j < r <= i /\ from_option (fun c => exists v, return_at tpc c v) False (etr !! r).

  Global Instance pcr_dec etr i τ m: Decision (previous_calls_return etr i τ m).
  Proof using. Admitted.
    
  Context (ic: @trace_ctx heap_lang).
  Let ii := tctx_index ic.
  Let tc := tctx_tpctx ic. 
  Let Ki := tpctx_ctx tc.
  Let τi := tpctx_tid tc. 

  Context (m: val) (ai: val).

  Record fits_inf_call (etr: execution_trace heap_lang): Prop := FIC {
    fic_call: from_option (fun c => call_at tc c m ai (APP := App)) True (etr !! ii);
    fic_cont: forall j, ii <= j -> from_option (nval_at tc) True (etr !! j);
    fic_never_val: forall i, from_option (fun e => to_val e = None) True
            (from_option (fun c => from_locale c.1 τi) None (etr !! i));
    fic_main: ii < trace_length etr -> previous_calls_return etr ii τi m;
  }.

  Lemma fits_inf_call_last_or_short etr
    (FITS: fits_inf_call etr):
    (nval_at tc (trace_last etr)) \/ trace_length etr <= ii. 
  Proof using.
    edestruct Nat.lt_ge_cases as [LT| ]; [| by eauto].
    destruct FITS. 
    ospecialize * (fic_cont0 (trace_length etr - 1)).
    { lia. }
    rewrite trace_lookup_last in fic_cont0. 
    2: { lia. }
    simpl in fic_cont0. by left.
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
    destruct FITS as [II FITS NVAL MAIN]. split. 
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
    - intros LEN j K' ? PREV CALL. 
      destruct (etr !! j) as [c0| ] eqn:JTH; [| done]. simpl in CALL.
      (* destruct CALL as (a & CALL). *)
      ospecialize (MAIN _ j K' _ _).
      1, 2: simpl in *; lia.
      { erewrite LOOKUP; eauto. }
      destruct MAIN as (r&?&RET).
      opose proof * (trace_lookup_lt_Some_2 etr r) as [? RTH]. 
      { lia. }
      exists r. split; auto. rewrite RTH /=.
      erewrite LOOKUP in RET; eauto.  
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
    destruct FITS as [_ NEXT _].
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
    intros. pose proof (FIC etr).

    Ltac step_dec_proof := match goal with
    | H : ?P -> ?Q |- _ => destruct (@decide P) as [Y | N]; 
                        [try by solve_decision |
                         specialize (H Y); clear Y |
                         right; intros [???]; tauto] end
      .
    step_dec_proof.
    { destruct (etr !! ii); solve_decision. }
    step_dec_proof.
    { apply Decision_iff_impl with (P := Forall (fun j => from_option (nval_at tc) True (etr !! j)) (seq ii (trace_length etr - tctx_index ic))).
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
      simpl in *. lia. }
    step_dec_proof.
    { apply Decision_iff_impl with
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
      apply H0. split; [lia| ].
      eapply trace_lookup_lt_Some_1; eauto. }
    step_dec_proof.
    by left.
  Qed. 

End FitsInfCall. 
