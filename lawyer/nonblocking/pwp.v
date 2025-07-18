From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From trillium.program_logic Require Import execution_model weakestpre adequacy simulation_adequacy_em_cond. 
From trillium.prelude Require Import classical.
From fairness Require Import fairness.
From lawyer Require Import program_logic sub_action_em action_model.
From lawyer.examples Require Import orders_lib obls_tactics.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination.
From heap_lang Require Import lang.
From lawyer.nonblocking Require Import trace_context.


Close Scope Z.


Definition LoopingModel: Model :=
  {| mstate := unit; mlabel := unit; mtrans := fun _ _ _ => True |}.

(* Class LoopIrisG {Λ: language} Σ := { *)
(*     lig_inner :: irisG Λ LoopingModel Σ *)
(* }. *)


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


Section SimpleExample.

  Definition mk_ref: val :=
    λ: "v",
      let: "l" := ref "v" in
      "l"
  .

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.

  Context (d: Degree). 

  Lemma mk_ref_spec τ π q (a: val):
    {{{ cp_mul π d 5 ∗ th_phase_frag τ π q }}}
        mk_ref a @ τ
    {{{ (l: loc), RET #l; l ↦ a ∗ th_phase_frag τ π q }}}.
  Proof using.
    iIntros (Φ) "(CPS & PH) POST". rewrite /mk_ref. 
    pure_steps.
    wp_bind (ref _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply wp_alloc. iModIntro. iIntros (l) "L _".
    MU_by_burn_cp.
    pure_steps.
    wp_bind (Rec _ _ _)%E. pure_steps.
    iApply "POST". by iFrame.
  Qed.

End SimpleExample.


(* Section WaitFreeSpec. *)

(*   Instance OP_HL_WF: OP_HL unit unit WF_SB := {| om_hl_OPRE := OPP_WF |}. *)

(*   Notation "'Degree'" := (om_hl_Degree).  *)
(*   Notation "'Level'" := (om_hl_Level). *)
(*   Let d0: Degree := tt. *)

(*   Definition om_wfree_init (i: nat): ProgressState. *)
(*   Admitted. *)

(*   (* TODO: support invariants in precondition *) *)
(*   (* TODO: relax to non-trivial degrees *) *)
(*   (* TODO: remove phases? *) *)
(*   Definition wait_free_spec (m: val) := *)
(*     exists N,  *)
(*       forall {M EM} Σ {OHE: OM_HL_Env OP_HL_WF EM Σ}  *)
(*         τ π q (a: val), *)
(*       let _ := @IEM_irisG _ M HeapLangEM EM Σ _ in *)
(*       {{{ cp_mul π d0 N ∗ th_phase_frag τ π q }}} *)
(*         m a @ τ *)
(*       {{{ v, RET v; th_phase_frag τ π q }}}. *)

(*   Lemma mk_ref_WF_spec: wait_free_spec mk_ref. *)
(*   Proof using. *)
(*     red. exists 5. intros. *)
(*     iIntros "(CPS & PH) POST". *)
(*     iApply (mk_ref_spec with "[-POST]"). *)
(*     { iFrame. } *)
(*     iIntros "!> % (?&?)". iApply "POST". iFrame. *)
(*   Qed. *)

(* End WaitFreeSpec. *)

Definition WF_SB := 1.

Instance OPP_WF: ObligationsParamsPre (bounded_nat 2) unit WF_SB.
esplit; try by apply _.
- apply nat_bounded_PO.
- apply unit_PO.
Defined.

Section WFAdequacy.

  Let OP := LocaleOP (OPRE := OPP_WF) (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.
  Notation "'Degree'" := (bounded_nat 2). 
  Notation "'Level'" := (unit).

  Let d0: Degree. refine (ith_bn 2 0 _). abstract lia. Defined. 
  Let d1: Degree. refine (ith_bn 2 1 _). abstract lia. Defined. 
  Let l0: Level := tt.

  Let M := AM2M ObligationsAM.
  Let ASEM := ObligationsASEM.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} τ _ => obls τ ∅ (oGS := aGS)).

  Context (ic: @trace_ctx heap_lang).
  Context (m: val).

  Definition no_extra_obls (_: cfg heap_lang) (δ: mstate M) :=
    forall τ', default ∅ (ps_obls δ !! τ') ≠ ∅ -> τ' = tctx_tid ic.

  Definition obls_sim_rel_wfree extr omtr :=
    obls_sim_rel extr omtr /\ no_extra_obls (trace_last extr) (trace_last omtr).

  Definition wfree_trace_inv `{Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (extr: execution_trace heap_lang) (omtr: auxiliary_trace M): iProp Σ :=
    ⌜ no_extra_obls (trace_last extr) (trace_last omtr) ⌝.

  Definition fits_inf_call: execution_trace heap_lang → Prop.
  Admitted.

  Definition PR_wfree {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (iG := IEM_irisG HeapLangEM EM)
    : ProgressResource state_interp wfree_trace_inv fork_post fits_inf_call.
  Admitted.

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

  (* Hypotheses (WF_LVL: well_founded (strict lvl_le)) (WF_DEG: well_founded (strict deg_le)). *)

  Theorem simple_om_simulation_adequacy_terminate_multiple_waitfree Σ
        `{hPre: @heapGpreS Σ M EM} (s: stuckness)
        es σ1 (s1: mstate M) p
        (INIT: em_is_init_st (es, σ1) s1 (ExecutionModel := EM))
        (extr : extrace heap_lang)
        (Hexfirst : trfirst extr = (es, σ1))
        (LEN: length es ≥ 1):
    PR_premise_multiple obls_sim_rel_wfree fits_inf_call Σ s es σ1 s1 (p: @em_init_param _ _ EM) ->
    extrace_valid extr -> 
    fair_ex (tctx_tid ic) extr ->
    terminating_trace extr \/ exists k, ¬ fits_inf_call (trace_take_fwd k extr).
  Proof.
    intros Hwp VALID FAIR.
    
    pose proof (om_simulation_adequacy_model_trace_multiple_waitfree
                Σ _ es _ s1 _ INIT _ VALID Hexfirst LEN Hwp) as ADEQ.
    destruct ADEQ as [(mtr & MATCH & OM0) | RET]. 
    2: { right. done. } 
    left. 
    opose proof (obls_matching_traces_OM _ _ _ _ MATCH _) as (omtr & MATCH'' & SR & OM_WF & FIRST'').
    { intros ?? X. apply X. }
    { simpl in INIT. rewrite OM0. eapply obls_init_wf; eauto. }
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

  Definition init_om_wfree_state (c: cfg heap_lang): ProgressState.
  Admitted.

  (* TODO: rename *)
  Lemma obls_terminates_impl_multiple_waitfree Σ {HEAP: @heapGpreS Σ M EM}
    (extr : extrace heap_lang) a
    (ETR0: exists e0, (trfirst extr).1 = [subst "m" m e0])
    (VALID: extrace_valid extr)
    (FAIR: fair_ex (tctx_tid ic) extr)
    (CALL: call_at extr m ic a)
    :
    terminating_trace extr \/ has_return extr ic. 
  Proof.
    destruct ETR0 as (?& X).
    destruct (trfirst extr) as [? σ] eqn:ETR0. simpl in X. subst. 
    unshelve opose proof (simple_om_simulation_adequacy_terminate_multiple_waitfree Σ NotStuck
                  _ _ _ _
                  _ _ ETR0 _ _ _ _) as ADEQ; eauto.
    { exact (init_om_wfree_state (trfirst extr)). }
    { admit. }
    { admit. }

    destruct ADEQ; [tauto| ].
    right. red.
    destruct ic. simpl in *.

  Admitted.
  
  (* Theorem mk_ref_wait_free: *)
  (*   forall etr, *)
  (*   (exists e0, (trfirst etr).1 = [subst "m" mk_ref e0]) -> *)
  (*   extrace_valid etr -> always_returns etr mk_ref. *)
  (* Proof using. *)
  (*   intros etr CLIENT VALID. red. intros τ FAIR i K a. *)
  (*   red. intros CALL. *)
  (*   epose proof (Classical_Prop.classic _) as [X | NORET]; [by apply X| ]. *)
  (*   assert (infinite_trace etr) as INF. *)
  (*   { clear -CALL NORET FAIR. *)
  (*     pose proof (trace_has_len etr) as [len LEN]. *)
  (*     eapply infinite_trace_equiv; eauto. *)
  (*     destruct len; [done| ]. *)
  (*     admit. }     *)
  (*   (* assert (forall j, j <= i -> expr_under_expr etr (TraceCtx j τ K)) as ALW. *) *)
  (*   (* { intros j LE. red. *) *)
  (*   (*   admit. } *) *)
   
  (*   (* pose proof not_exists_forall_not. *) *)
  (*   (* fold all in H.  *) *)
  (*   (* Ltac not_ex_into_all_not H :=  *) *)
  (*   (*   pose proof @not_exists_forall_not as Y; *) *)
  (*   (*   specialize (Y _ _ H); simpl in Y; clear H; simpl in Y; rename Y into H.  *) *)
  (*   (* not_ex_into_all_not INF.  *) *)
  (*   (* apply (@not_exists_forall_not _ (fun (j: nat) => _) _) in INF.  *) *)
  (*   (* by_classical_contradiction *) *)

  (*   assert (∃ omtr, exec_OM_traces_match etr omtr ∧ om_tr_wf omtr /\ trfirst omtr = om_wfree_init i) as (omtr & MATCH & WF & OM0). *)
  (*   { admit. } *)
    

End WFAdequacy.
