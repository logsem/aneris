From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl gmultiset big_op mono_nat gmap_view.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len trace_utils. 
From trillium.program_logic Require Import execution_model weakestpre adequacy simulation_adequacy_em_cond. 
From trillium.prelude Require Import classical.
From fairness Require Import fairness locales_helpers utils.
From lawyer Require Import program_logic sub_action_em action_model.
From lawyer.examples Require Import orders_lib obls_tactics.
From lawyer.nonblocking Require Import trace_context om_wfree_inst pr_wfree_lib (* pr_wfree *) wfree_traces wptp_gen pwp calls wfree_adequacy_lib.
(* From lawyer.nonblocking.logrel Require Import fundamental.  *)
From lawyer.nonblocking.logrel Require Import valid_client.
From lawyer.nonblocking.tokens Require Import om_wfree_inst_tokens.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination.
From heap_lang Require Import lang simulation_adequacy.


Close Scope Z. 

(* TODO: use in other file *)
Definition is_fun (v: val) := exists f x b, v = RecV f x b. 


Section WFAdequacy.

  Let OP := LocaleOP (OPRE := OPP_WF) (Locale := locale heap_lang). 
  Existing Instance OP.
  Let OM := ObligationsModel.

  Let M := AM2M ObligationsAM.
  Let ASEM := ObligationsASEM.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} _ _ => ⌜ True ⌝%I).

  Context (ic: @trace_ctx heap_lang).
  Let ii := tctx_index ic.
  Let tpc := tctx_tpctx ic. 
  Let Ki := tpctx_ctx tpc.
  Let τi := tpctx_tid tpc. 

  Context (s': stuckness).
  
  Context `(SPEC: WaitFreeSpecToken ms).
  Context (m: val) (MSm: m ∈ dom ms). 
  Let F := wfst_F _ SPEC.
  
  Context ((* m *) ai: val).

  Let fic := fits_inf_call ic m ai.

  Definition is_init_tpool (tp: list expr) :=
    Forall (fun e => exists e0, e = subst "m" m e0 /\ valid_client e0) tp /\
    (ii = 0 -> exists e, from_locale tp τi = Some e /\ under_ctx Ki e = Some (m ai)) /\
    (forall e, from_locale tp τi = Some e -> to_val e = None).

  Definition wfreeΣ: gFunctors := iemΣ HeapLangEM EM. 

  Instance wfree_pre: @heapGpreS wfreeΣ M EM.
  Proof. 
    unshelve esplit. 
  Qed. 

  Lemma PR_premise_wfree `{hPre: @heapGpreS Σ M EM} c
    (ETR0: is_init_tpool c.1)
    (MOD_INIT: wfst_is_init_st _ SPEC c)
    (M_FUN: is_fun m)
    :
  PR_premise_multiple (obls_sim_rel_wfree ic s') (fits_inf_call ic m ai)
    Σ MaybeStuck c.1 c.2
    (init_om_wfree_state F ic c) ((): @em_init_param _ _ EM).
  Proof using. Admitted.

  (* TODO: rename *)
  Lemma simple_om_simulation_adequacy_terminate_multiple_waitfree_impl extr
    (MOD_INIT : wfst_is_init_st _ SPEC (trfirst extr))
    (VALID : extrace_valid extr)
    (FAIR : fair_call extr tpc ii)
    (INIT_TP : is_init_tpool (trfirst extr).1)
    (CALL: from_option (fun c => call_at tpc c m ai (APP := App)) False (extr S!! ii))
    (M_FUN: is_fun m):
    terminating_trace extr /\ int_ref_inf_one (call_progresses ic s') extr ∨
    (∃ k, ¬ fits_inf_call ic m ai (trace_take_fwd k extr)) \/
    (s' = MaybeStuck /\ gets_stuck_ae extr ic). 
  Proof using.
    clear MSm.
    opose proof (om_simulation_adequacy_model_trace_multiple_waitfree
                   ic s'
                wfreeΣ _ (trfirst extr).1 _ _ _ _ _ _ _ VALID _ _) as ADEQ.
    { apply init_om_wfree_is_init. }
    { apply surjective_pairing. }     
    { rewrite -surjective_pairing. 
      eapply PR_premise_wfree; eauto. }
    
    destruct ADEQ as [(mtr & MATCH & OM0 & IREF) | RET].
    2: { right. left. done. } 

    opose proof (obls_matching_traces_OM _ _ _ _ MATCH _) as (omtr & MATCH'' & SR & OM_WF & FIRST'').
    { intros ?? X. apply X. }
    { eapply obls_init_wf. rewrite OM0. apply init_om_wfree_is_init. }

    destruct (Classical_Prop.classic (∃ j, has_return_at extr ic j)) as [[j RET]| NORET].
    { red in RET. rewrite (ic_helper ic) in RET.
      destruct RET as (r & cj & ? & JTH & RET).
      right. left. exists j. intros [_ NVALS _]. 
      specialize (NVALS _ H).

      eapply trace_take_fwd_lookup_Some' in JTH.
      2: reflexivity.
      rewrite JTH /= in NVALS.
      edestruct not_return_nval; eauto. }

    assert (int_ref_inf_one (call_progresses ic s') extr) as IREF1.
    { eapply int_ref_inf_proj_one. eapply int_ref_inf_impl; eauto.
      by intros ?? (?&?&?). }

    destruct (extr S!! ii) as [ci | ] eqn:IITH.
    2: { left.
         pose proof (trace_has_len extr) as [??]. 
         eapply state_lookup_dom_neg in IITH; eauto.
         split; [| done].
         eapply terminating_trace_equiv; eauto.
         destruct x; try done. }

    add_case (exists N, ii <= N /\ is_Some (extr S!! N) /\ ∀ j, N ≤ j → from_option (not_stuck_tid τi) True (extr S!! j)) IF_NS. 
    { intros NS. 
    
      assert (forall τ, obls_trace_fair τ omtr) as OM_FAIR.
      { eapply om_trace_fair; eauto. }

      left. split; [| done]. 
      pose proof (traces_match_valid2 _ _ _ _ _ _ MATCH'') as OM_VALID.
      pose proof (obls_fair_trace_terminate _ OM_VALID OM_FAIR) as OM_TERM.
      
      eapply (traces_match_preserves_termination _ _ _ _ _ _ MATCH'').
      apply OM_TERM; eauto.
      + apply unit_WF.
      + apply fin_wf. }

    destruct (decide (s' = MaybeStuck)) as [S'|S']. 
    2: { apply IF_NS. 
         exists ii. split; [lia| ]. split; [done| ].
         intros.
         destruct (extr S!! j) eqn:ITH; [| done]. simpl.
         eapply ref_call_progress_last; eauto. by destruct s'. }
    
    destruct (Classical_Prop.classic (gets_stuck_ae extr ic)) as [| NS]. 
    { do 2 right. tauto. }
    apply IF_NS.

    rewrite /gets_stuck_ae in NS.
    rewrite not_all_ex_not_iff in NS. destruct NS as (N & NS).
    apply not_impl_and_not_iff in NS as ([? NTH] & NS).
    exists (max ii N). split; [lia| ].
    split.
    { pose proof (Nat.max_spec_le ii N) as [[? MAX] | [? MAX]]; rewrite MAX; eauto. }
    intros. destruct (extr S!! j) eqn:JTH; [| done]. simpl.
    
    rewrite not_ex_all_not_iff in NS.
    specialize (NS j). rewrite /ge in NS. rewrite !not_and_l in NS.
    destruct NS as [? | [? | NS]].
    { lia. }
    { set_solver. }
    rewrite /gets_stuck_at /= in NS.
    rewrite (ic_helper ic) /tpc (tc_helper ic) in NS.
    rewrite JTH in NS.
    destruct (decide (not_stuck_tid τi c)); [done| ]. destruct NS.
    eexists. repeat split.
    { lia. }
    apply stuck_tid_neg. split; eauto.
    opose proof * from_locale_trace.
    { done. }
    { apply IITH. }
    { simpl in CALL.
      move CALL at bottom. do 2 red in CALL.
      rewrite /tpc tc_helper /= in CALL.
      apply mk_is_Some in CALL. apply CALL. }
    { etrans; [| apply H]. lia. }
    by rewrite JTH in H0.
  Qed.

  Theorem simple_om_simulation_adequacy_terminate_multiple_waitfree extr
        (ETR0: valid_init_tpool_restr (trfirst extr).1 ms)
        (MOD_INIT: wfst_is_init_st _ SPEC (trfirst extr))
        (CALL: from_option (fun c => call_at tpc c m ai (APP := App)) False (extr S!! ii))
    :
    extrace_valid extr -> 
    fair_call extr tpc ii ->
    (exists f x b, m = RecV f x b) ->
    terminating_trace extr /\ int_ref_inf_one (call_progresses ic s') extr \/ 
    (exists k, ¬ fits_inf_call ic m ai (trace_take_fwd k extr)) \/
    (s' = MaybeStuck /\ gets_stuck_ae extr ic). 
  Proof.
    intros VALID FAIR M_FUN. 

    destruct (decide (ii = 0 → ∃ e,
                    from_locale (trfirst extr).1 τi = Some e ∧ under_ctx Ki e = Some (m ai))) as [II0| ].
    2: { pose proof tc_helper. 
         clear -n H.
         right. left. 
         apply Classical_Prop.imply_to_and in n as (II & NO0).
         exists 0. intros FITS. apply NO0.
         destruct FITS.
         fold ii in fic_call.
         rewrite trace_take_fwd_0_first in fic_call.
         rewrite II /= in fic_call.
         red in fic_call. simpl in fic_call. eauto.
         red in fic_call. rewrite H in fic_call.
         eexists. split; eauto. by rewrite under_ctx_fill. }

    destruct (@decide (∀ e, from_locale (trfirst extr).1 τi = Some e → to_val e = None)) as [E0| ].
    { destruct (from_locale (trfirst extr).1 τi) eqn:E.
      2: { left. set_solver. }
      destruct (to_val e) eqn:V.
      { right. set_solver. }
      left. set_solver. }
    2: { apply not_forall_exists_not in n as [e VAL].
         apply Classical_Prop.imply_to_and in VAL as [E VAL].
         right. left. exists 0. intros FITS. apply VAL.
         destruct FITS. 
         specialize (fic_never_val 0). rewrite trace_take_fwd_0_first /= in fic_never_val.
         rewrite E in fic_never_val. done. }

    assert (is_init_tpool (trfirst extr).1) as INIT_TP.
    { repeat split; eauto.
      red in ETR0.
      (* should follow from ETR0 *)
      admit. }

    by apply simple_om_simulation_adequacy_terminate_multiple_waitfree_impl.
  Admitted.

  (* TODO: rename *)
  Lemma obls_terminates_impl_multiple_waitfree
    (extr : extrace heap_lang)
    (ETR0: valid_init_tpool_restr (trfirst extr).1 ms)
    (MOD_INIT: wfst_is_init_st _ SPEC (trfirst extr))
    (VALID: extrace_valid extr)
    (FAIR: fair_call extr tpc ii)
    (MAIN: previous_calls_return_tr extr ii τi m)
    (CALL: from_option (fun c => call_at tpc c m ai (APP := App)) False (extr S!! ii))
    (M_FUN: is_fun m)
    :
    terminating_trace extr /\ int_ref_inf_one (call_progresses ic s') extr
    \/ has_return extr ic \/
    (s' = MaybeStuck /\ gets_stuck_ae extr ic). 
  Proof.
    opose proof * (simple_om_simulation_adequacy_terminate_multiple_waitfree) as ADEQ; eauto.

    destruct ADEQ as [| [[n NFIT] | STUCK]]; [tauto| | tauto]. 
    right. left. red. simpl in *.
    
    destruct (extr S!! ii) as [ci | ] eqn:ITH; rewrite ITH /= in CALL; [| done].
    by eapply not_fic_has_return.
  Qed.
    
End WFAdequacy.

Theorem wfree_token_is_wait_free_restr ms
  (SPEC: WaitFreeSpecToken ms)
  (FUNS: map_Forall (const ∘ is_fun) ms)
  :
  wait_free_restr ms (wfst_is_init_st _ SPEC) (* s' *) NotStuck any_arg.
Proof using.
  red. intros etr ETR0 MOD_INIT VALID. intros m IN.
  
  apply main_returns_reduction; try done.
  { (* TODO: prove above separately? *)
    apply elem_of_dom in IN as [??]. eapply FUNS; eauto. }
  
  red. intros [i tpc] a ci FAIR ITH MAIN CALL _.

  opose proof * (obls_terminates_impl_multiple_waitfree (TraceCtx i tpc)
                   NotStuck
                ) as ADEQ.
  3: by apply MOD_INIT. 
  all: eauto.
  { simpl. by rewrite ITH. }
  { apply elem_of_dom in IN as [??]. eapply FUNS; eauto. }
    
  destruct ADEQ as [[TERM PROGRESS]| [? | ?]].
  2, 3: tauto. 

  pose proof (trace_has_len etr) as [? LEN].
  eapply terminating_trace_equiv in TERM as [len EQ]; eauto. subst.
  opose proof (proj2 (state_lookup_dom _ _ LEN (len - 1)) _) as [c LAST].
  { apply trace_len_gt_0 in LEN. simpl in *. lia. }
  
  assert (i <= len - 1) as DOM.
  { pose proof ITH as DOM.
    eapply mk_is_Some, state_lookup_dom in DOM; eauto. simpl in DOM.
    lia. }

  add_case (not_stuck_tid (tpctx_tid tpc) c) IF_NS.
  { intros NS.
    left.
    edestruct @Classical_Prop.classic as [RET | NORET]; [by apply RET| ].

    clear PROGRESS.
        
    pose proof DOM as EE. eapply from_locale_trace in EE; eauto.
    2: { eapply locales_of_cfg_Some. eapply expr_at_in_locales.
         erewrite <- surjective_pairing. eauto. }
    rewrite LAST /= in EE. destruct EE as [e EE].
    
    destruct (decide (nval_at tpc c)) as [NVAL | VAL]. 
    + clear ITH CALL MOD_INIT VALID ETR0 SPEC MAIN.
      eapply has_return_fin_trace; eauto. 
    + eapply call_returns_if_not_continues in DOM; eauto.
      2: { eapply call_nval_at; eauto. done. }
      destruct DOM as (k & r & ck & RANGE & KTH & RETk).
      red. exists k, r, ck. split; eauto. lia. }
  
  (* destruct s'. *)
  (* 2: { destruct (decide (not_stuck_tid (tpctx_tid tpc) c)). *)
  (*      { by apply IF_NS. } *)
  (*      right. split; auto.          *)
  (*      red. intros N [? NTH]. *)
  (*      exists (len - 1). repeat split; eauto. *)
  (*      { red. eapply mk_is_Some, state_lookup_dom in NTH; eauto. *)
  (*        simpl in NTH. lia. } *)
  (*      red. destruct tpc. *)
  (*      eexists. repeat split; eauto. *)
  (*      apply stuck_tid_neg. split; auto. *)
  (*      eapply from_locale_trace in DOM; eauto. *)
  (*      by rewrite LAST in DOM. } *)
  
  apply IF_NS.
  eapply ref_call_progress_last in PROGRESS; eauto. 
Qed.
