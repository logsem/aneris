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
  Proof. Admitted. 
    
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
