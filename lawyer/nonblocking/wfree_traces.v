From iris.proofmode Require Import tactics.
From fairness Require Import locales_helpers utils fairness.
From lawyer.nonblocking Require Import trace_context calls.
From lawyer.nonblocking.logrel Require Import valid_client.
From heap_lang Require Import lang notation locales_helpers_hl.
From trillium.traces Require Import exec_traces trace_lookup inftraces.

Close Scope Z.


From fairness Require Import fin_branch. 

(* TODO: move *)
Lemma list_approx_impl {A: Type} (P Q: A -> Prop)
  (IMPL: forall a, Q a -> P a):
  list_approx P -> list_approx Q.
Proof using.
  intros [l APX]. exists l.
  intros. set_solver.
Qed.

(* TODO: move, use to prove pcr_dec and not_stuck_dec (for heap_lang) *)
(* TODO: simplify *)
Lemma eq_fill_item_fin e: list_approx (fun xy => fill_item xy.1 xy.2 = e).
Proof using.
  eapply list_approx_impl with (P := fun '(Ki, e') => under_ctx_item Ki e = Some e').
  { intros [??] ?. eapply under_ctx_item_spec; eauto. }
  destruct e; simpl.
  all: try by (exists []; intros [Ki ?]; by destruct Ki).
  - exists (cprod [AppLCtx (default #0 (to_val e2)); AppRCtx e1] [e1; e2]).
    intros [Ki ?]. destruct Ki; try done. 
    all: simpl; rewrite /calls.check; destruct decide; set_solver.
  - exists [(UnOpCtx op, e)]. intros [??].
    destruct e0; simpl; try done.
    rewrite /calls.check; destruct decide; set_solver.
  - exists (cprod [BinOpLCtx op (default #0 (to_val e2)); BinOpRCtx op e1] [e1; e2]).
    intros [Ki ?]. destruct Ki; try done. 
    all: simpl; rewrite /calls.check; destruct decide; set_solver.
  - exists [(IfCtx e2 e3, e1)].
    intros [Ki ?].
    destruct Ki; try done. simpl.
    rewrite /calls.check; destruct decide; set_solver.
  - exists (cprod [PairLCtx (default #0 (to_val e2)); PairRCtx e1] [e1; e2]).
    intros [Ki ?]. destruct Ki; try done. 
    all: simpl; rewrite /calls.check.
    + destruct e2; try done. destruct decide; set_solver.
    + destruct decide; set_solver.
  - exists [(FstCtx, e)]. 
    intros [Ki ?].
    destruct Ki; try done. simpl.
    set_solver.
  - exists [(SndCtx, e)]. 
    intros [Ki ?].
    destruct Ki; try done. simpl.
    set_solver.
  - exists [(InjLCtx, e)]. 
    intros [Ki ?].
    destruct Ki; try done. simpl.
    set_solver.
  - exists [(InjRCtx, e)]. 
    intros [Ki ?].
    destruct Ki; try done. simpl.
    set_solver.
  - exists [(CaseCtx e2 e3, e1)].
    intros [Ki ?].
    destruct Ki; try done. simpl.
    rewrite /calls.check; destruct decide; set_solver.
  - exists (cprod [AllocNLCtx (default #0 (to_val e2)); AllocNRCtx e1] [e1; e2]).
    intros [Ki ?]. destruct Ki; try done. 
    all: simpl; rewrite /calls.check.
    + destruct e2; try done. destruct decide; set_solver.
    + destruct decide; set_solver.
  - exists [(FreeCtx, e)]. 
    intros [Ki ?].
    destruct Ki; try done. simpl.
    set_solver.
  - exists [(LoadCtx, e)]. 
    intros [Ki ?].
    destruct Ki; try done. simpl.
    set_solver.
  - exists (cprod [StoreLCtx (default #0 (to_val e2)); StoreRCtx e1] [e1; e2]).
    intros [Ki ?]. destruct Ki; try done. 
    all: simpl; rewrite /calls.check.
    + destruct e2; try done. destruct decide; set_solver.
    + destruct decide; set_solver.
  - exists (cprod [CmpXchgLCtx (default #0 (to_val e2)) (default #0 (to_val e3));
              CmpXchgMCtx e1 (default #0 (to_val e3));
              CmpXchgRCtx e1 e2
         ] [e1; e2; e3]).
    intros [Ki ?]. destruct Ki; try done. 
    all: simpl; rewrite /calls.check.
    + destruct e2, e3; try done. destruct decide; set_solver.
    + destruct e3; try done. destruct decide; set_solver.
    + destruct decide; set_solver.
  - exists (cprod [FaaLCtx (default #0 (to_val e2)); FaaRCtx e1] [e1; e2]).
    intros [Ki ?]. destruct Ki; try done. 
    all: simpl; rewrite /calls.check.
    + destruct e2; try done. destruct decide; set_solver.
    + destruct decide; set_solver.
Qed.


(* TODO: upstream? *)
Lemma rev_empty_inv {A: Type} (l: list A):
  rev l = [] <-> l = [].
Proof using.
  pose proof (length_rev l).
  rewrite -!length_zero_iff_nil.
  lia.
Qed.

(* TODO: upstream? *)
Lemma list_empty_or_snoc {A: Type} (l: list A):
  l = [] \/ exists t l', l = l' ++ [t].
Proof using.
  destruct (rev l) eqn:RL.
  - left. by apply rev_empty_inv.
  - right. exists a, (rev l0).
    apply rev_inj. rewrite RL.
    rewrite rev_app_distr. by rewrite rev_involutive.
Qed.

Lemma eq_fill_fin (e: expr): list_approx (fun xy => fill xy.1 xy.2 = e).
Proof using.  
  remember (expr_depth e) as D. generalize dependent e.
  pattern D. apply lt_wf_rect. clear D. simpl.  
  intros n IH e D.
  pose proof (eq_fill_item_fin e) as [l APX].

  assert {l': list (ectx_item * expr) |
          forall a, a ∈ l' <-> fill_item a.1 a.2 = e} as [l' L']. 
  { exists (filter (fun (a : ectx_item * expr) => fill_item a.1 a.2 = e) l).
    intros ?. rewrite elem_of_list_filter. set_solver. }

  subst n.
  clear l APX.

  assert (forall x, x ∈ l' -> list_approx (λ y, fill y.1 y.2 = x.2)) as REC.
  { intros [Ki e'] IN. simpl.
    eapply IH; [| reflexivity].
    eapply L' in IN. subst.
    apply fill_item_depth. }

  assert (forall x, (list_approx (λ y, fill y.1 y.2 = x.2) * (x ∈ l')%type) + (x ∉ l')) as REC'.
  { intros x. simpl.
    destruct (@decide (x ∈ l')).
    { simpl in *. eapply traces.utils_logic.Decision_iff_impl.
      { symmetry. apply L'. }
      apply _. }
    - left. split; auto.
    - right. auto. }

  simpl in *.
  set (extract := (fun x =>
                           let (Ki, e') := (x: ectx_item * expr) in 
                           let subs := REC' x in
                           let subs': list (ectx heap_lang * expr) := 
                             match subs with 
                             | inl lst => proj1_sig lst.1
                             | inr _ => []
                             end in
                           let exts: list (ectx heap_lang * expr) :=
                             map (fun '(K', e'') => (K' ++ [Ki], e'')) subs'
                           in exts
                      )).   
  
  set (extracted := map extract l'). 

  exists ((ectx_emp, e) :: flat_map id extracted).
  intros [K e'] EQ.
  (* subst.  *)
  simpl in EQ.
  destruct (list_empty_or_snoc K) as [-> | (t & K' & ->)].
  { set_solver. }
  simpl in EQ. rewrite fill_app /= in EQ.
  right.
  apply elem_of_list_In, in_flat_map. simpl.
  assert (In (t, fill K' e') l') as INt.
  { apply elem_of_list_In. by apply L'. }
  exists (extract (t, (fill K' e'))). split.
  - subst extracted. apply in_map_iff. eexists. split; [reflexivity| ].
    apply INt. 
  - apply in_map_iff. eexists (_, _).
    split; [reflexivity| ].
    destruct (REC' (t, fill K' e')) as [[[l'' APX''] IN] | NOTIN].
    2: { destruct NOTIN. by apply elem_of_list_In. }
    simpl.
    apply elem_of_list_In. apply APX''. simpl. done.
Qed.
  
Lemma eq_fill_fin' (e: expr): list_approx (fun K => exists e', fill K e' = e).
Proof using.
  destruct (eq_fill_fin e) as [l APX].
  exists l.*1. intros K [e' EQ].
  apply elem_of_list_fmap. eexists (_, _). split.
  2: { eapply APX; eauto. }
  done.
Qed.
 
Section CallInTrace.

  (** parameterized with additional restriction on client
      to unify with token version *)
  Definition valid_op_client (P: expr -> Prop) (m: val) e :=
    exists e0, e = subst "m" m e0 /\ valid_client e0 /\ P e0.

  Context (m: val).
  
  Definition has_return_at (tr: extrace heap_lang) '(TraceCtx i tpc as tc) j :=
    exists r cj, i <= j /\ tr S!! j = Some cj /\ return_at tpc cj r.

  Definition has_return tr tc := exists j, has_return_at tr tc j.

  Definition gets_stuck_at (tr: extrace heap_lang) '(TraceCtx i (TpoolCtx _ τ)) j :=
    exists cj, i <= j /\ tr S!! j = Some cj /\ stuck_tid τ cj.

  Definition gets_stuck_once tr tc := exists j, gets_stuck_at tr tc j.
  (** this stronger condition is necessary to prove main call reduction *)
  Definition gets_stuck_ae tr tc :=
    forall N, is_Some (tr S!! N) -> exists j, j >= N /\ is_Some (tr S!! j) /\ gets_stuck_at tr tc j.

  Lemma gets_stuck_ae_stronger tr tc:
    gets_stuck_ae tr tc -> gets_stuck_once tr tc.
  Proof using.
    intros STUCK. red.
    ospecialize * (STUCK 0 _).
    { by rewrite state_lookup_0. }
    destruct STUCK as (?&?&?&?). eauto.
  Qed.

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

  (** In the end we want to quantify over all threads,
      but making it an explicit parameter here allows to reuse this def
      for restricted wait-freedom *)
  Definition always_returns (s: stuckness) (P: val -> Prop) (τ: locale heap_lang) tr :=    
    forall i K a ci,
      let tpc := TpoolCtx K τ in
      let tc := TraceCtx i tpc in
      fair_call tr tpc i ->
      tr S!! i = Some ci ->
      call_at tpc ci m a (APP := App) ->
      P a -> 
      has_return tr tc \/ s = MaybeStuck /\ gets_stuck_ae tr tc. 

  Definition valid_init_tpool (tp: list expr) := Forall (valid_op_client (fun _ => True) m) tp.
  
  Definition wait_free (is_init_st: cfg heap_lang -> Prop)
    (s: stuckness) (P: val -> Prop) := forall etr,
      valid_init_tpool (trfirst etr).1 ->
      is_init_st (trfirst etr) ->
      extrace_valid etr ->
      forall τ, always_returns s P τ etr.

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
         destruct (Classical_Prop.classic (not_stuck_tid τ ck)) as [NSTUCK | STUCK].
         2: { exists 0. rewrite Nat.add_0_r.
              eexists. split; eauto.
              red. left. intros (?&?). by apply STUCK. }
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
    destruct (Classical_Prop.classic (not_stuck_tid τ c)) as [NS | STUCK].
    2: { exists 0. right. rewrite Nat.add_0_r KTH /=.
         apply stuck_tid_neg. split; auto.
         eapply from_locale_trace in LE; eauto.
         by rewrite KTH /= in LE. } 
         
    ospecialize * FAIR; eauto.
    { odestruct (Classical_Prop.classic (locale_enabled_safe _ _ )) as [EN | DIS]; [by apply EN| ].
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
    apply Classical_Prop.not_and_or in DIS as [DIS | STUCK].
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

  Definition always_returns_strong s P τ tr :=
    forall i K a ci,
      let tpc := TpoolCtx K τ in
      let tc := TraceCtx i tpc in
      fair_call_strong tr tpc i ->
      tr S!! i = Some ci ->
      call_at tpc ci m a (APP := App) ->
      P a -> 
      has_return tr tc \/ s = MaybeStuck /\ gets_stuck_ae tr tc. 

  Definition wait_free_strong (is_init_st: cfg heap_lang -> Prop) s P := forall etr,
      valid_init_tpool (trfirst etr).1 ->
      is_init_st (trfirst etr) ->
      extrace_valid etr ->
      forall τ, always_returns_strong s P τ etr.

  Lemma wait_free_equiv C s P:
    wait_free C s P <-> wait_free_strong C s P.
  Proof using.
    rewrite /wait_free /wait_free_strong.
    repeat (apply forall_proper; intros).
    (* destruct x3 as [? [??]].  *)
    split; intros RET **; apply RET; auto.
    all: eapply fair_call_strenghten; eauto;
      rewrite H0 /=; exists x6; eauto.
  Qed.

  Global Instance no_return_before_dec etr κ i j: Decision (no_return_before etr κ i j).
  Proof using.
    rewrite /no_return_before.
    apply not_dec. apply ex_fin_dec with (l := seq i (S $ j - i)).
    2: { intros ? [? RET].
         destruct RET as (r & cj & ? & JTH & RET).
         apply in_seq. lia. }
    intros. apply and_dec; [solve_decision| ].
    rewrite /has_return_at.
    destruct (decide (i <= a)).
    2: { right. by intros (?&?&?&?&?). }
    destruct (etr S!! a) eqn:ATH.
    2: { right. by intros (?&?&?&?&?). }
    rewrite /return_at.
    rewrite /expr_at. destruct κ as [K τ]. simpl.
    destruct (from_locale c.1 τ) eqn:TT. 
    2: { right. intros (?&?&?&?&?). set_solver. }
    destruct (under_ctx K e) eqn:KE.
    2: { erewrite under_ctx_spec_neg in KE.
         right. intros (?&?&?&?&?). set_solver. }
    apply under_ctx_spec in KE.
    destruct (to_val e0) eqn:VV.
    2: { right. intros (?&?&?&?&?).
         inversion H0. subst. rewrite TT in H1.
         inversion H1. apply ectx_fill_inj in H3. by subst. }
    apply of_to_val in VV as <-. subst e. 
    left. eauto.
  Qed.

  Definition any_arg: val -> Prop := fun _ => True. 

  Lemma always_returns_impl etr s1 s2 P1 P2 τ
    (S12: stuckness_le s1 s2)
    (P21: forall v, P2 v -> P1 v):
    always_returns s1 P1 τ etr -> always_returns s2 P2 τ etr.
  Proof using.
    rewrite /always_returns. simpl.
    intros AR i K **.
    ospecialize * (AR i K); eauto.
    destruct AR as [| (->&?)]; [by left| ].
    destruct s2; try done. by right.
  Qed.
  
  Lemma wait_free_impl C1 C2 s1 s2 P1 P2
    (C21: forall c, C2 c -> C1 c)
    (S12: stuckness_le s1 s2)
    (P21: forall v, P2 v -> P1 v):
    wait_free C1 s1 P1 -> wait_free C2 s2 P2.
  Proof using.
    rewrite /wait_free. simpl. intros WF ? INIT ?? ?.
    eapply always_returns_impl; eauto.
  Qed.
  
End CallInTrace.


Section RestrWFree.

  Definition valid_init_tpool_restr (tp: list expr) (MS: gmultiset val) :=
    (* TODO: allow "smaller" thread pools too *)
    Forall2 (valid_op_client no_forks) (elements MS) tp.

  (** TODO: account for multiple m's in unrestricted wait-freedom too *)
  Definition wait_free_restr (MS: gmultiset val) (is_init_st: cfg heap_lang -> Prop)
    s P := forall etr,
      valid_init_tpool_restr (trfirst etr).1 MS ->
      is_init_st (trfirst etr) ->
      extrace_valid etr ->
      forall τ m, elements MS !! τ = Some m -> always_returns m s P τ etr.

End RestrWFree.


Section FitsInfCall.

  (* TODO: do we need a similar def for infinite traces? *)
  Definition previous_calls_return (etr: execution_trace heap_lang) i τ m :=
    forall j K, let tpc := TpoolCtx K τ in
           j < i ->
           from_option (fun c => exists a, call_at tpc c m a (APP := App)) False (etr !! j) ->
           exists r, j < r <= i /\ from_option (fun c => exists v, return_at tpc c v) False (etr !! r).

  Global Instance Decision_all_in_list_inf_helper `{EqDecision A} (P: A -> Prop) (l: list A)
    (IN: forall a, P a -> a ∈ l)
    (DEC: forall a, Decision (P a))
    (INF: finite.Finite A -> False)
    :
    Decision (forall a, P a).
  Proof using.
    assert {l': list A | forall a, a ∈ l' <-> P a} as [l' IN']. 
    { exists (filter P l). intros ?. rewrite elem_of_list_filter. set_solver. }
    clear l IN. 
    eapply traces.utils_logic.Decision_iff_impl.
    { apply forall_proper. intros ?. apply IN'. }
    simpl.
    right. intros FIN. destruct INF.
    exists (remove_dups l').
    { by apply NoDup_remove_dups. }
    intros. by apply elem_of_remove_dups.
  Qed.

  Global Instance Decision_impl_all_helper {A: Type} (P Q: A -> Prop) (l: list A)
    (IN: forall a, P a -> a ∈ l)
    (DECP: forall a, Decision (P a))
    (DECQ: forall a, Decision (Q a))
    :
    Decision (forall a, P a -> Q a).
  Proof using.
    destruct (decide (Forall (fun a => P a -> Q a) l)).
    - left. intros.
      eapply Forall_forall in f; eauto.
    - right. intros ALL.
      apply n.
      eapply Forall_forall; eauto.
  Qed.

  Global Instance pcr_dec etr i τ m: Decision (previous_calls_return etr i τ m).
  Proof using.
    rewrite /previous_calls_return.
    eapply traces.utils_logic.Decision_iff_impl.
    { do 2 (eapply forall_proper; intros).
      apply ZifyClasses.impl_morph; [| reflexivity].
      Unshelve. 2: exact (x ∈ seq 0 i).
      rewrite elem_of_seq. lia. }
    simpl.
    eapply traces.utils_logic.Decision_iff_impl.
    { symmetry. rewrite forall_prod_helper.
      setoid_rewrite curry_uncurry_prop. reflexivity. }
    
    apply Decision_impl_all_helper with
      (l := cprod (seq 0 i) 
              (flat_map (fun i => from_option (fun c => from_option (fun e => (proj1_sig (eq_fill_fin e)).*1) [] (from_locale c.1 τ)) [] (etr !! i)) 
                 (seq 0 i))).
    { simpl. intros [??] [IND VAL].
      simpl in *. apply elem_of_list_cprod. split; [done| ]. 
      simpl. apply elem_of_list_In, in_flat_map.
      eexists. split.
      { apply elem_of_list_In. eauto. }
      destruct (etr !! n); try done. simpl in *.
      destruct VAL as [a CALL]. rewrite CALL /=.
      apply elem_of_list_In.
      destruct (eq_fill_fin (fill l (m a))) as [items APX] eqn:ITEMS.
      rewrite ITEMS. simpl in *.
      opose proof * (APX (_, _)); eauto.
      apply elem_of_list_fmap. eexists. by split; eauto. }
    { intros [??]. simpl. apply and_dec; try solve_decision.
      destruct (etr !! n); try solve_decision.
      simpl. destruct (from_locale c.1 τ) eqn:TT; rewrite TT.
      2: { right. by intros (? & [=]). }
      destruct (under_ctx l e) eqn:CC.
      2: { right. rewrite under_ctx_spec_neg in CC.
           intros (? & [=]). set_solver. }
      assert ({a': val | e0 = m a'} + {forall (v: val), e0 ≠ m v}) as VV. 
      { clear. destruct e0.
        all: try by (right; intros ? ?).
        destruct (decide (of_val m = e0_1)).
        - subst. Set Printing Coercions. 
          destruct (to_val e0_2) eqn:V2.
          + left. exists v. f_equal.
            symmetry. by apply of_to_val. 
          + right. intros ? ?. inversion H.
            subst. done.  
        - right. intros ? ?. inversion H. by subst. }
      apply under_ctx_spec in CC.
      destruct VV as [[? ->] | NEQ].
      - subst. left. eauto.
      - right. intros (?&?). inversion H. subst.
        apply fill_inj in H1. subst. set_solver. }
    { intros [??]. simpl.
      apply ex_fin_dec with (l := seq 0 (S i)).
      2: { intros. apply in_seq. lia. }
      intros a. apply and_dec; try solve_decision.
      destruct (etr !! a); try solve_decision.
      simpl. destruct (from_locale c.1 τ) eqn:TT; rewrite TT.
      2: { right. by intros (? & [=]). }
      destruct (under_ctx l e) eqn:CC.
      2: { right. rewrite under_ctx_spec_neg in CC.
           intros (? & [=]). set_solver. }
      apply under_ctx_spec in CC. subst.
      destruct (to_val e0) eqn:V2.
      + left. exists v. f_equal.
        f_equal. symmetry. by apply of_to_val. 
      + right. intros (?&?). inversion H.
        apply fill_inj in H1. subst. set_solver. }
  Qed.
    
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
