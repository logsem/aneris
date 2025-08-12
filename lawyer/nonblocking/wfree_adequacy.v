From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From trillium.program_logic Require Import execution_model weakestpre adequacy simulation_adequacy_em_cond. 
From trillium.prelude Require Import classical.
From fairness Require Import fairness.
From lawyer Require Import program_logic sub_action_em action_model.
From lawyer.examples Require Import orders_lib obls_tactics.
From lawyer.nonblocking Require Import trace_context om_wfree_inst mk_ref pr_wfree.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination.
From heap_lang Require Import lang.


Close Scope Z.


Section CallInTrace.
  Context (tr: extrace heap_lang). 
  Context (m: val). (** the method under consideration *)
  
  Definition expr_under '(TraceCtx i τ K) (e: expr) :=
    exists c, tr S!! i = Some c /\ from_locale c.1 τ = Some (ectx_fill K e).

  Definition call_at tc (a: val) :=
    expr_under tc (App (of_val m) (of_val a)). 

  Definition return_at tc (r: val) :=
    expr_under tc (of_val r).

  (* TODO: rename *)
  Definition expr_under_expr tc :=
    exists e, expr_under tc e /\ to_val e = None. 
  
  Definition has_return '(TraceCtx i τ K as tc) :=
    exists j r, i <= j /\ return_at (TraceCtx j τ K) r.

  Definition always_returns := 
    forall tc a, fair_ex (tctx_tid tc) tr -> call_at tc a -> has_return tc.
  
End CallInTrace.


(* TODO: support invariants in precondition *)
(* TODO: relax to non-trivial degrees *)
(* TODO: remove phases? *)
Definition wait_free_spec (m: val) :=
  exists N,
  forall {M EM} Σ {OHE: OM_HL_Env OP_HL_WF EM Σ}
    τ π q (a: val),
    let _ := @IEM_irisG _ M HeapLangEM EM Σ _ in
    {{{ cp_mul π d_wfr0 N ∗ th_phase_frag τ π q }}}
      m a @ τ
    {{{ v, RET v; th_phase_frag τ π q }}}.


Section WFAdequacy.

  (* Let OP := LocaleOP (OPRE := OPP_WF) (Locale := locale heap_lang). *)
  (* Existing Instance OP. *)
  (* Let OM := ObligationsModel. *)
  (* Notation "'Degree'" := (bounded_nat 2).  *)
  (* Notation "'Level'" := (unit). *)

  Let OP := LocaleOP (OPRE := OPP_WF) (Locale := locale heap_lang). 
  Existing Instance OP.
  Let OM := ObligationsModel.

  Let M := AM2M ObligationsAM.
  Let ASEM := ObligationsASEM.
  (* Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} τ _ => obls τ ∅ (oGS := aGS)). *)
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} _ _ => ⌜ True ⌝%I).

  Context (ic: @trace_ctx heap_lang).
  Context (m: val).

  Definition no_extra_obls (_: cfg heap_lang) (δ: mstate M) :=
    forall τ', default ∅ (ps_obls δ !! τ') ≠ ∅ -> τ' = tctx_tid ic.

  Definition obls_sim_rel_wfree extr omtr :=
    obls_sim_rel extr omtr /\ no_extra_obls (trace_last extr) (trace_last omtr).

  Definition wfree_trace_inv `{Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (extr: execution_trace heap_lang) (omtr: auxiliary_trace M): iProp Σ :=
    ⌜ no_extra_obls (trace_last extr) (trace_last omtr) ⌝.

  (* Definition fits_inf_call: execution_trace heap_lang → Prop. *)
  (* Admitted. *)
  Context (F: nat). 

  Definition fits_inf_call := fits_inf_call ic m F. 

  (* Definition PR_wfree {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} *)
  (*   (iG := IEM_irisG HeapLangEM EM) *)
  (*   : ProgressResource state_interp wfree_trace_inv fork_post fits_inf_call. *)
  (* Admitted. *)

  Instance fic_dec: ∀ ex, Decision (fits_inf_call ex).
  Proof. Admitted.

  Lemma fic_fpc: filter_pref_closed fits_inf_call.
  Proof. Admitted.

  Definition obls_st_rel_wfree c δ := obls_st_rel c δ /\ no_extra_obls c δ. 

  Definition obls_om_traces_match_wfree: extrace heap_lang -> trace (mstate M) (mlabel M) -> Prop :=
    obls_om_traces_match_gen obls_st_rel_wfree. 

  Theorem om_simulation_adequacy_model_trace_multiple_waitfree Σ
        `{hPre: @heapGpreS Σ M EM} (s: stuckness)
        (es: list expr) σ1 (s1: mstate M) p
        (INIT: em_is_init_st (es, σ1) s1 (ExecutionModel := EM))
        (extr : extrace heap_lang)
        (Hvex : extrace_valid extr)
        (Hexfirst : trfirst extr = (es, σ1))
        (LEN: length es ≥ 1):
    PR_premise_multiple obls_sim_rel_wfree fits_inf_call Σ s es σ1 s1 (p: @em_init_param _ _ EM) ->
    (∃ omtr, obls_om_traces_match_wfree extr omtr ∧ trfirst omtr = s1) \/
    (exists k, ¬ fits_inf_call (trace_take_fwd k extr)).
  Proof using.
    intros PREM.

    unshelve epose proof (@PR_strong_simulation_adequacy_traces_multiple _ _ EM 
                            HeapLangEM obls_sim_rel_wfree fits_inf_call
                            _ _ _ _ _ 
                            s es σ1 s1 p
                extr
                Hvex
                ltac:(done)
                obls_ves_wrapper
                obls_st_rel_wfree
                (fun oτ '(_, τ') => oτ = τ')
                _ _ _ _ _ _ _
                PREM
      ) as SIM.
    { apply fic_fpc. }
    { simpl. intros ????[??]? STEP.
      red in STEP. simpl in STEP. destruct STEP as [STEP ->].
      destruct o; [| done].
      simpl in STEP. red in STEP. apply STEP. }
    { simpl. intros ????[??]? STEP.
      red in STEP. simpl in STEP. destruct STEP as [STEP ->].
      destruct o; [| done].
      simpl in STEP. red in STEP.
      constructor. apply STEP. }
    { simpl. intros ?? SIM.
      split; apply SIM. }
    { simpl. intros ?? SIM. apply SIM. }
    { done. }
    { eapply adequacy_utils.rel_finitary_impl; [| apply obls_sim_rel_FB].
      2, 3: by apply _.
      intros ?? X. apply X. }
    { done. }

    done.
  Qed.

  Definition init_om_wfree_state (c: cfg heap_lang): ProgressState.
  Admitted.

  Lemma init_om_wfree_is_init c:
    obls_is_init_st c (init_om_wfree_state c).
  Proof using. Admitted. 

  Lemma PR_premise_wfree `{hPre: @heapGpreS Σ M EM} c
        (ETR0: exists e0, c.1 = [subst "m" m e0])
        (SPEC: wait_free_spec m):
  PR_premise_multiple obls_sim_rel_wfree fits_inf_call Σ MaybeStuck c.1 c.2
    (init_om_wfree_state c) ((): @em_init_param _ _ EM).
  Proof using.    
    red. iIntros (Hinv) "(PHYS & MOD)". simpl.
    iModIntro.
    iExists wfree_trace_inv.
    iExists (PR_wfree ic m F). simpl. 

    rewrite !bi.sep_assoc. iSplitL.
    2: { rewrite /adequacy_cond.rel_always_holds_with_trace_inv.

         iIntros (extr omtr [tp σ] EXTRA FIN NSTUCK).
         simpl. iIntros "(%VALID_STEP & HEAP & MSI & [%TH_OWN %OBLS]) POSTS #INV".
         red in EXTRA. destruct EXTRA as (VALID & EX0 & OM0 & CONT_SIM). 
         iApply fupd_mask_intro_discard; [done| ].

         rewrite /wfree_trace_inv. iDestruct "INV" as %NOOBS'.
         rewrite /obls_sim_rel_wfree. iSplit; [| done].  


         destruct extr.
         { iPureIntro.
           simpl in VALID_STEP.
           inversion VALID. subst.
           red in EX0, OM0. simpl in EX0, OM0. subst.
           rewrite /obls_sim_rel_wfree /obls_sim_rel /obls_sim_rel_gen.
           simpl.

           split; [done| ]. simpl. red.
           (* (* apply om_live_tids_init. *) *)
           (* apply LIVE0.  *)

           (* should follow from init_om_wfree_state def *)
           admit.  
         }
         
         (* Unset Printing Notations. *)

         (* rewrite prefixes_simpl. *)
         (* rewrite -map_app. rewrite -seq_app. *)
         (* rewrite -Nat.le_add_sub.  *)
         
         simpl in VALID_STEP. inversion VALID. subst. simpl in *.
         (* red in EX_FIN. simpl in EX_FIN. subst. simpl. *)
         rewrite /obls_sim_rel. iSplit.
         { simpl. iPureIntro. 
           destruct a. done. }
         simpl. rewrite /obls_st_rel.

         iPureIntro.
         red. simpl. intros τ OB.
         red in NOOBS'. red in OB. specialize (NOOBS' _ OB).
         admit. (* can also enforce with trace invariant *)
         (* iApply (no_obls_live_tids_multiple with "[$] [$]"); try done. *)
         (* eapply valid_exec_length. *)
         (* { eapply valid_system_trace_valid_exec_trace; eauto. } *)
         (* all: eauto.          *)
         
  Admitted.

  Definition wfreeΣ: gFunctors.
  Admitted.

  Instance wfree_pre: @heapGpreS wfreeΣ M EM.
  Admitted. 

  Theorem simple_om_simulation_adequacy_terminate_multiple_waitfree extr
        (ETR0: exists e0, (trfirst extr).1 = [subst "m" m e0])
        (SPEC: wait_free_spec m):
    extrace_valid extr -> 
    fair_ex (tctx_tid ic) extr ->
    terminating_trace extr \/ exists k, ¬ fits_inf_call (trace_take_fwd k extr).
  Proof.
    intros VALID FAIR.
    destruct ETR0 as [e0 ETR0]. 

    opose proof (om_simulation_adequacy_model_trace_multiple_waitfree
                wfreeΣ _ (trfirst extr).1 _ _ _ _ _ VALID _ _ _) as ADEQ.
    { apply init_om_wfree_is_init. }
    { apply surjective_pairing. }
    { rewrite ETR0. simpl. lia. } 
    { rewrite -surjective_pairing. 
      eapply PR_premise_wfree; eauto. }
    
    destruct ADEQ as [(mtr & MATCH & OM0) | RET]. 
    2: { right. done. } 
    left. 
    opose proof (obls_matching_traces_OM _ _ _ _ MATCH _) as (omtr & MATCH'' & SR & OM_WF & FIRST'').
    { intros ?? X. apply X. }
    { eapply obls_init_wf. rewrite OM0. apply init_om_wfree_is_init. }
 
    assert (forall τ, obls_trace_fair τ omtr) as OM_FAIR.
    { intros.
      destruct (decide (τ = tctx_tid ic)) as [-> | NEQ].
      { eapply exec_om_fairness_preserved; eauto. }
      red. apply fair_by_equiv. red. intros n OB.
      destruct (omtr S!! n) eqn:NTH; rewrite NTH in OB; [| done].
      simpl in OB.
      eapply traces_match_state_lookup_2 in NTH; eauto.
      destruct NTH as (?&NTH'& NOOBS).
      red in NOOBS. destruct NOOBS as [_ NOOBS].
      red in NOOBS. ospecialize (NOOBS τ _).
      { red in OB. by destruct lookup. }
      subst. tauto. }

    pose proof (traces_match_valid2 _ _ _ _ _ _ MATCH'') as OM_VALID.
    pose proof (obls_fair_trace_terminate _ OM_VALID OM_FAIR) as OM_TERM.

    eapply (traces_match_preserves_termination _ _ _ _ _ _ MATCH'').
    apply OM_TERM; eauto.
    + apply unit_WF.
    + apply fin_wf.
  Qed.

  (* TODO: rename *)
  Lemma obls_terminates_impl_multiple_waitfree
    (extr : extrace heap_lang) a
    (ETR0: exists e0, (trfirst extr).1 = [subst "m" m e0])
    (VALID: extrace_valid extr)
    (FAIR: fair_ex (tctx_tid ic) extr)
    (CALL: call_at extr m ic a)
    (SPEC: wait_free_spec m)
    :
    terminating_trace extr \/ has_return extr ic. 
  Proof.
    opose proof * (simple_om_simulation_adequacy_terminate_multiple_waitfree) as ADEQ; eauto.

    destruct ADEQ; [tauto| ].
    right. red.
    destruct ic. simpl in *.

  Admitted.
     
End WFAdequacy.


Definition wait_free (m: val) := forall etr,
    (exists e0, (trfirst etr).1 = [subst "m" m e0]) ->
    extrace_valid etr ->
    always_returns etr m.

Theorem wfree_is_wait_free m
  (SPEC: wait_free_spec m):
  wait_free m. 
Proof using.
  red. intros etr ETR0 VALID.
  red. intros tc a FAIR CALL. 

  eapply simple_om_simulation_adequacy_terminate_multiple_waitfree in ETR0; eauto.
  destruct ETR0 as [TERM | NO_INF_CALL].
  - (** if it's finite, then τ should've reduced to a value *)
    admit. 
  - (** if it's finite, see above *)
    (** if it's infinite, there must've been return at k *)
    admit. 
Admitted.


Lemma mk_ref_WF_spec: wait_free_spec mk_ref.
Proof using.
  red. exists 5. intros.
  iIntros "(CPS & PH) POST".
  iApply (mk_ref_spec with "[-POST]").
  { iFrame. }
  iIntros "!> % (?&?)". iApply "POST". iFrame.
Qed.


Theorem mk_ref_is_wait_free: wait_free mk_ref.
Proof using.
  apply wfree_is_wait_free.
  apply mk_ref_WF_spec.
Qed.
