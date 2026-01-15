From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl gmultiset big_op mono_nat gmap_view.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len trace_utils. 
From trillium.program_logic Require Import execution_model int_ref.
From trillium.prelude Require Import classical.
From fairness Require Import fairness locales_helpers utils.
From lawyer Require Import program_logic sub_action_em action_model.
From lawyer.examples Require Import orders_lib obls_tactics.
From lawyer.nonblocking Require Import trace_context om_wfree_inst pr_wfree_lib wfree_traces calls.
From lawyer.nonblocking.logrel Require Import fundamental. 
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am.
From heap_lang Require Import lang simulation_adequacy.


Close Scope Z.


Section Lib.
  Open Scope WFR_scope. 

  Context (F: nat).
  Context (ic: @trace_ctx heap_lang).
  Let ii := tctx_index ic.
  Let tpc := tctx_tpctx ic. 
  Let Ki := tpctx_ctx tpc.
  Let τi := tpctx_tid tpc. 

  Definition init_om_wfree_state
    (c: cfg heap_lang): ProgressState :=
    let CPS := (2 * F + ii) *: {[+ d0 +]} ⊎ {[+ d1 +]} in
    let δ0 := init_om_state c CPS 0 in
    let s0 := (0: SignalId) in
    let obls' := if (decide (τi ∈ locales_of_cfg c))
                 then (<[ τi := {[ s0 ]} ]> (ps_obls δ0)) else ps_obls δ0 in
    let sigs' := (if (decide (τi ∈ locales_of_cfg c)) then {[ s0 := (l0, false) ]} else ∅)
                 ∪ ps_sigs δ0 in
    let eps' := (if (decide (τi ∈ locales_of_cfg c)) then {[ (s0, π0, d0) ]} else ∅)
                ∪ ps_eps δ0 in
    update_obls obls' $ update_sigs sigs' $ update_eps eps' δ0. 

  Lemma init_om_wfree_is_init
    (* F TI d0 d1 τi l0 ii *)
    c:
    obls_is_init_st c (init_om_wfree_state 
                         (* F TI d0 d1 τi l0 ii  *)
                         c).
  Proof using.
    clear. 
    red. rewrite /init_om_wfree_state. split.
    { destruct decide.
      2: { destruct c. apply init_om_state_init_multiple. }
      simpl. rewrite dom_insert_L dom_gset_to_gmap. set_solver. }
    split; simpl. 
    - red. simpl.
      pose proof (dom_ipa c) as D. simpl in D. rewrite D. 
      destruct decide. 
      2: { by rewrite dom_gset_to_gmap. } 
      rewrite dom_insert_L !dom_gset_to_gmap.
      set_solver.
    - red. simpl.
      rewrite map_union_empty.
      destruct decide. 
      2: { by rewrite map_filter_empty. }
      rewrite map_filter_singleton /= dom_singleton_L.
      rewrite map_img_insert_L flatten_gset_union. set_solver.
    - eapply dpd_ipa; eauto. 
    - eapply cpb_init_phases_π0; eauto. 
    - red. simpl.
      destruct decide; [| set_solver].
      rewrite union_empty_r_L. setoid_rewrite elem_of_singleton. 
      intros (?& π &?&?&->&LT). simpl in *.
      pose proof (phase_le_init π) as GE. 
      by apply strict_spec, proj2 in LT.
    - red. simpl. rewrite map_union_empty.
      destruct decide. 
      2: by rewrite flatten_gset_map_img_gtg_empty. 
      rewrite map_img_insert_L.
      rewrite -gset_to_gmap_difference_singleton.
      rewrite flatten_gset_union.
      by rewrite flatten_gset_map_img_gtg_empty. 
    - red. simpl. 
      intros ???.
      destruct (_ !! τ1) eqn:X, (_ !! τ2) eqn:Y; simpl; try done.
      destruct decide. 
      2: { apply lookup_gset_to_gmap_Some in X as [? <-]. 
           apply lookup_gset_to_gmap_Some in Y as [? <-].
           done. }
      rewrite lookup_insert_Some in X. rewrite lookup_insert_Some in Y.
      destruct X as [[<- <-] | [NEQX X]], Y as [[<- <-] | [NEQY Y]];
        (try apply lookup_gset_to_gmap_Some in X as [? <-]);
        (try apply lookup_gset_to_gmap_Some in Y as [? <-]);
        done.
    
  Qed.

  Lemma obls_τi_enabled c δ
    (NOOBS': no_extra_obls ic c δ)
    (NVAL: from_option (λ e : expr, to_val e = None) True (from_locale c.1 τi))
    (TH_OWN: locales_of_cfg c = dom (ps_obls δ))
    (τ : nat)
    (OBS : has_obls τ δ):
  locale_enabled τ (c.1, c.2).
  Proof using.
    red.
    pose proof OBS as OBS_. apply NOOBS' in OBS_. subst τ.
    simpl. destruct from_locale eqn:LOC.
    { eauto. }
    simpl in NVAL.
    eapply set_eq in TH_OWN.
    apply not_iff_compat, proj1 in TH_OWN.
    edestruct TH_OWN.
    - intros ?%locales_of_cfg_Some; eauto.
      + erewrite LOC in H. by destruct H.
      + apply inhabitant.
    - eapply elem_of_dom; eauto. red in OBS.
      destruct lookup; done.
  Qed.

  (** for simplicity, we forget about the specific phases *)
  Lemma init_wfree_resources_weak `{!ObligationsGS Σ} c:
    obls_init_resource (init_om_wfree_state c) () -∗
    (cp_mul π0 d0 (2 * F) ∗ cp_mul π0 d0 ii ∗ cp π0 d1) ∗
    (⌜ τi ∈ locales_of_cfg c ⌝ →
     ∃ s, obls τi {[ s ]} ∗ sgn s l0 (Some false) ∗ ep s π0 d0) ∗
    ([∗ set] τ ∈ locales_of_cfg c ∖ {[ τi ]}, obls τ ∅) ∗
    ([∗ set] τ ∈ locales_of_cfg c, ∃ π, th_phase_eq τ π).  
  Proof using.
    iIntros "INIT". 
    rewrite /obls_init_resource /init_om_wfree_state. simpl.
    rewrite union_empty_r_L map_union_empty. 
    iDestruct "INIT" as "(CPS & SIGS & OB & EPS & PH & EB)".
    iSplitL "CPS".
    { rewrite mset_map_disj_union. rewrite mset_map_mul.
      iDestruct (big_sepMS_disj_union with "CPS") as "[CPS0 CP1]".
      rewrite !mset_map_singleton.
      rewrite big_sepMS_singleton. iFrame.
      rewrite -cp_mul_split. by iApply cp_mul_alt. }
    rewrite bi.sep_assoc. 
    iSplitL "SIGS OB EPS".
    { rewrite /obls_map_repr. 
      destruct decide.
      2: { rewrite difference_disjoint_L; [| set_solver].
           iSplitR.
           { by iIntros (?). }
           by iApply empty_obls_helper. }
      rewrite gmap_insert_delete_union.
      rewrite map_fmap_union.
      rewrite -gset_to_gmap_difference_singleton.
      rewrite <- @gmap_disj_op_union.
      2: { apply map_disjoint_dom. do 2 rewrite dom_fmap.
           rewrite dom_singleton_L dom_gset_to_gmap. set_solver. }
      rewrite auth_frag_op own_op.
      iDestruct "OB" as "[OB OB']". iDestruct (empty_obls_helper with "[$]") as "$".
      iIntros (?).
      rewrite map_fmap_singleton. by iFrame. }

    pose proof (dom_ipa c) as D. simpl in D. rewrite -D. 
    iApply big_sepM_dom. iApply (big_sepM_impl with "[$]"). set_solver.  
  Qed.

  (* TODO: move *)
  Lemma RecV_App_not_stuck (mm a: val) c e τ K
    (M_FUN: ∃ f x b, mm = (rec: f x := b)%V)
    (EXPR: from_locale c.1 τ = Some e)
    (CALL: under_ctx K e = Some (mm a)):
  not_stuck_tid τ c.
  Proof using.
    destruct M_FUN as (?&?&?&->). 
    red. eexists.
    split; eauto.
    apply under_ctx_spec in CALL. subst e.
    destruct c. 
    red. right. red. do 3 eexists.
    simpl.
    econstructor; eauto.
    simpl. by apply BetaS.
  Qed.

  Context (s': stuckness).

  Definition obls_sim_rel_wfree extr omtr :=
    obls_sim_rel extr omtr /\ no_extra_obls ic (trace_last extr) (trace_last omtr) /\
    call_progresses ic s' extr. 

  Definition obls_st_rel_wfree c δ := 
    obls_st_rel c δ /\ no_extra_obls ic c δ. 

  Lemma tc_helper:
    tctx_tpctx ic = {| tpctx_ctx := Ki; tpctx_tid := τi |}.
  Proof using. clear. by destruct ic as [? []]. Qed.

  Lemma ic_helper:
    ic = {| tctx_tpctx := tpc; tctx_index := ii |}.
  Proof using. clear.  by destruct ic. Qed.

  (* Local Lemma tpc_helper: *)
  (*   tpc = {| tpctx_ctx := Ki; tpctx_tid := τi |}. *)
  (* Proof using. clear. by destruct ic as [? []]. Qed. *)

  Lemma om_trace_fair 
    (extr: extrace heap_lang)
    (VALID : extrace_valid extr)
    (FAIR : fair_call extr tpc ii)
    (omtr : obls_trace)
    (MATCH'' : exec_OM_traces_match extr omtr)
  (SR: traces_match (λ (_ : olocale heap_lang) (_ : mlabel ObligationsModel), True)
      obls_st_rel_wfree
      (λ (_ : cfg heap_lang) (_ : olocale heap_lang) (_ : cfg heap_lang), True)
      (λ (_ : AM2M ObligationsAM) (_ : mlabel ObligationsModel) 
         (_ : AM2M ObligationsAM), True)
      extr omtr)
  (NORET : ¬ ∃ j : nat, has_return_at extr ic j)
  (IITH : is_Some (extr S!! ii))
  (PROGRESS: exists N, ii <= N /\ is_Some (extr S!! N) /\ ∀ j, N ≤ j → from_option (not_stuck_tid τi) True (extr S!! j))
    :
  ∀ τ, obls_trace_fair τ omtr.
  Proof using.
    intros. destruct (decide (τ = τi)) as [-> | NEQ].
    2: { red. apply fair_by_equiv. red. intros n OB.
         destruct (omtr S!! n) eqn:NTH; rewrite NTH in OB; [| done].
         simpl in OB.
         eapply traces_match_state_lookup_2 in NTH; eauto.
         destruct NTH as (?&NTH'& NOOBS).
         red in NOOBS. destruct NOOBS as [_ NOOBS].
         red in NOOBS. ospecialize (NOOBS τ _).
         { red in OB. by destruct lookup. }
         subst. tauto. }
    
    red. apply fair_by_equiv. red. intros n OB.
    destruct (omtr S!! n) eqn:NTH; rewrite NTH in OB; [| done].
    simpl in OB.
    eapply traces_match_state_lookup_2 in NTH; eauto.
    destruct NTH as (?&NTH'& NOOBS).
    red in NOOBS. apply proj1 in NOOBS. do 2 red in NOOBS.
    specialize (NOOBS _ OB). simpl in NOOBS. 
    
    red in FAIR. move FAIR at bottom. 
    rewrite /tpc tc_helper in FAIR.
    
    rewrite /no_return_before in FAIR. 
    rewrite -tc_helper -ic_helper in FAIR.
    
    destruct PROGRESS as (N & LE_N & NTH & PROGRESS). 

    assert (exists cm: cfg heap_lang, extr S!! (max n N) = Some cm) as [cm MTH].
    { edestruct (Nat.max_spec_le n N) as [[? ->] | [? ->]]; eauto. }
    destruct (decide (locale_enabled τi cm)) as [ENm | DISm].
    2: { (* there must've been a step between n and m*)
      opose proof * (enabled_disabled_step_between extr n) as STEP; eauto.
      { lia. }
      destruct STEP as (k & [LE BOUND] & STEP).
      apply Nat.le_sum in LE as [d ->].
      pose proof STEP as [[??] _]%mk_is_Some%label_lookup_states. 
      eapply obls_fairness_preservation.fairness_sat_ex_om_helper; eauto.
      { apply _. }
      rewrite STEP. simpl. red. right. eauto. }
    
    ospecialize (FAIR _ _ _ MTH _ _).
    { lia. }
    { split; auto.
      ospecialize (PROGRESS _). erewrite MTH in PROGRESS.
      apply PROGRESS. lia. }
    { intros (?&?&?). eauto. }
    
    destruct FAIR as (d & FAIR).
    destruct (max_plus_consume n N d) as [? EQ]. rewrite EQ in FAIR. 
    destruct FAIR as (c' & DTH & STEP).
    eapply obls_fairness_preservation.fairness_sat_ex_om_helper; eauto; try congruence.
    simpl.
    
    red. red in STEP. simpl. rewrite /tid_match in STEP.

    rewrite /locale_enabled_safe in STEP.
    rewrite and_comm in STEP. 
    rewrite not_and_l_alt in STEP. rewrite -or_assoc in STEP.
    destruct STEP; [| set_solver].
    destruct H.
    ospecialize (PROGRESS _). erewrite DTH in PROGRESS.
    apply PROGRESS. lia. 
  Qed.

  (* TODO: ? move, generalize *)
  Global Instance under_ctx_ex_dec (extr: extrace heap_lang) e':
    Decision (∃ e, from_locale (trfirst extr).1 τi = Some e ∧ under_ctx Ki e = Some e').
  Proof using.
    clear. 
    apply ex_fin_dec with
      (l := from_option (flip cons nil) [] (from_locale (trfirst extr).1 τi)).
    { solve_decision. }
    intros ? (RUNS & ?).
    simpl. rewrite RUNS. simpl. tauto.
  Qed.

  Lemma ref_call_progress_last tr i c
    (ITH: tr S!! i = Some c)
    (REF: int_ref_inf_one (call_progresses ic s') tr):
    s' = NotStuck -> ii <= i -> 
    not_stuck_tid τi c.
  Proof using.
    clear -ITH REF. 
    intros NS GE. 
    pose proof (trace_has_len tr) as [? LEN].
    pose proof ITH as LT. eapply mk_is_Some, state_lookup_dom in LT; eauto.
    assert (trace_length (trace_take_fwd i tr) = S i).
    { apply Nat.le_antisymm.
      1: by apply trace_take_fwd_length_bound.
      opose proof * (trace_take_fwd_length i tr); eauto.
      destruct x; try lia.
      rewrite H.
      simpl in LT. lia. }
    specialize (REF i). red in REF.    
    rewrite H in REF. ospecialize * REF; try (done || lia).
    symmetry in H. apply trace_lookup_last in H.
    eapply trace_take_fwd_lookup_Some' in ITH; [| reflexivity].
    set_solver.
  Qed.

  (* TODO: find existing *)
  Global Instance stuckness_eqdec: EqDecision stuckness.
  Proof using. red. intros [] []; (by left) || (by right). Qed.


  Lemma not_all_ex_not_iff: ∀ (A : Type) (P : A → Prop),
      ¬ (∀ x : A, P x) <-> ∃ x : A, ¬ P x.
  Proof using.
    split.
    - apply not_forall_exists_not.
    - apply Classical_Pred_Type.ex_not_not_all.
  Qed.

  Lemma not_ex_all_not_iff: ∀ (A : Type) (P : A → Prop), ¬ (∃ x : A, P x) <-> ∀ x : A, ¬ P x. 
  Proof using.
    split.
    - apply not_exists_forall_not. 
    - apply Classical_Pred_Type.all_not_not_ex. 
  Qed.

  Lemma not_impl_and_not_iff: ∀ P Q : Prop, ¬ (P → Q) <-> P ∧ ¬ Q.
  Proof using.
    clear. 
    split.
    - apply Classical_Prop.imply_to_and.
    - tauto.
  Qed.

  Lemma call_continues_or_returns tpc_ c1 c2 oτ
    (NVAL: nval_at tpc_ c1)
    (STEP: locale_step c1 oτ c2):
    nval_at tpc_ c2 \/ exists r, return_at tpc_ c2 r.
  Proof using.
    clear -NVAL STEP. 
    red in NVAL. destruct NVAL as (e & EXPR & NVAL).
    pose proof EXPR as [eτi TI]%expr_at_in_locales%locales_of_cfg_Some.
    2: by apply c1. 
    red in EXPR. destruct tpc_ as [K' τ'].  
    (* pose proof EXPR as [eτi TI]%expr_at_in_locales%locales_of_cfg_Some. *)
    (* 2: { by apply c1. } *)
    inversion STEP. subst. inversion H1.
    2: { by subst. }

    subst. simpl in *.
    destruct (decide (τ' = locale_of t1 (fill K e1'))).
    2: { left. exists e. split; auto.
         red. eapply locale_step_other_same; set_solver. } 

    subst τ'.
    rewrite /from_locale from_locale_from_locale_of in EXPR. inversion EXPR as [FILL'].
    rewrite FILL' in H1.
    apply fill_step_inv in H1; eauto. simpl in *.
    destruct H1 as (e' & EQ2 & STEP'). rewrite FILL' EQ2.

    rewrite /nval_at. simpl.
    erewrite locale_of_hl_expr_irrel.
    rewrite /from_locale. erewrite (from_locale_from_locale_of nil t1).

    destruct (to_val e') eqn:VAL; [| by eauto]. 
    right. exists v. Set Printing Coercions.
    erewrite of_to_val; eauto.
  Qed.

  Lemma call_returns_if_not_continues tpc_ i j ci cj etr
    (VALID: extrace_valid etr)
    (ITH: etr S!! i = Some ci)
    (CALL : nval_at tpc_ ci)
    (LE: i <= j)
    (JTH: etr S!! j = Some cj)
    (NOCONT: ¬ nval_at tpc_ cj)
    :
    exists k r ck, i < k <= j /\ etr S!! k = Some ck /\ return_at tpc_ ck r. 
  Proof using.
    clear dependent ic. 
    apply Nat.le_sum in LE as [d ->].    
    generalize dependent i. generalize dependent ci.
    induction d.
    { simpl. setoid_rewrite Nat.add_0_r. intros.
      rewrite ITH in JTH. inversion JTH. by subst. }
    intros.
    pose proof JTH as X.
    apply mk_is_Some, state_lookup_prev with (j := S i) in X as [ci' ITH']; [| lia].
    pose proof ITH' as [oτ ITHl]%mk_is_Some%label_lookup_states'.
    rewrite -Nat.add_1_r in ITH'.
    opose proof * (trace_valid_steps'' _ _ _ i) as STEP; eauto.
    { apply extrace_valid_alt in VALID; eauto. }
    eapply call_continues_or_returns in STEP; eauto.
    destruct STEP as [NVAL | [r RET]].
    2: { do 3 eexists. split; eauto. lia. }
    ospecialize (IHd _ NVAL _ ITH' _).
    { rewrite -JTH. f_equal. lia. }
    destruct IHd as (?&?&?&?&?&?).
    do 3 eexists. split; eauto. lia.
  Qed.

  (* TODO: try to remove duplication between this and previous_calls_return *)
  Definition previous_calls_return_tr (tr: extrace heap_lang) i τ m :=
    forall j K, let tpc := TpoolCtx K τ in
           j < i ->
           from_option (fun c => exists a, call_at tpc c m a (APP := App)) False (tr S!! j) ->
           exists r, j < r <= i /\ from_option (fun c => exists v, return_at tpc c v) False (tr S!! r). 

  Lemma extrace_valid_empty (extr: extrace heap_lang) σ
    (VALID: extrace_valid extr)
    (EMPTY: trfirst extr = ([], σ)):
    extr = ⟨ ([], σ) ⟩.
  Proof using.
    destruct extr; simpl in EMPTY; subst. 
    { done. }
    apply extrace_valid_alt, trace_valid_cons_inv, proj2 in VALID. 
    inversion VALID; subst; try done.
    inversion H. subst. clear -H3.
    apply (@f_equal _ _ length) in H3.
    rewrite !length_app /= in H3. lia.
  Qed.

  Lemma not_fic_has_return m ai extr n ci
    (VALID : extrace_valid extr)
    (MAIN : previous_calls_return_tr extr ii τi m)
    (NFIT : ¬ fits_inf_call ic m ai (trace_take_fwd n extr))
    (ITH : extr S!! ii = Some ci)
    (CALL : call_at tpc ci m ai (APP := App)):
    ∃ j, has_return_at extr ic j.
  Proof using. 
    pose proof (FIC ic m ai (trace_take_fwd n extr)) as X.
    rewrite !curry_uncurry_prop in X. apply Classical_Prop.imply_to_or in X.
    destruct X as [NFIT' | ?]; [| done]. clear NFIT. rename NFIT' into NFIT.
    apply Classical_Prop.not_and_or in NFIT as [X | NFIT].
    1: apply Classical_Prop.not_and_or in X as [X | NFIT].
    1: apply Classical_Prop.not_and_or in X as [NFIT | NFIT].
    - 
      destruct (trace_take_fwd n extr !! tctx_index ic) eqn:II; rewrite II /= // in NFIT.
      destruct NFIT.
      apply trace_take_fwd_lookup_Some in II.
      fold ii in II. rewrite II in ITH. inversion ITH. 
      eauto. 
    -
     
      apply not_forall_exists_not in NFIT. destruct NFIT as [r NFIT].
      apply Classical_Prop.imply_to_and in NFIT as [GE NFIT].
      destruct (trace_take_fwd n extr !! r) eqn:RR; rewrite RR /= // in NFIT.
      
      eapply call_returns_if_not_continues in NFIT; eauto.
      3: by apply trace_take_fwd_lookup_Some in RR.
      2: { eapply call_nval_at; eauto. done. }      
      rename r into b. 
      destruct NFIT as (k & r & ck & RANGE & KTH & RETk).
      rewrite ic_helper.
      exists k, r, ck. split; eauto. lia.
    -
     
      apply not_forall_exists_not in NFIT. destruct NFIT as [j NFIT].
      destruct (trace_take_fwd n extr !! j) eqn:JJ; rewrite JJ /= // in NFIT.
      destruct (from_locale c.1 τi) eqn:EE; rewrite EE /= // in NFIT.

      apply trace_take_fwd_lookup_Some in JJ. 

      destruct (Nat.le_gt_cases j ii) as [LE | GT].
      + destruct (to_val e) eqn:V; [| done].
        apply of_to_val in V. rewrite -V in EE.
        eapply val_preserved_trace in LE; eauto.
        rewrite ITH /= in LE.

        (* TODO: lemma? *)
        do 2 red in CALL. rewrite /tpc tc_helper in CALL.
        rewrite LE in CALL. inversion CALL.
        apply Some_inj in CALL. 
        apply (@f_equal _ _ to_val) in CALL.
        erewrite fill_not_val in CALL; done. 
      + apply Nat.lt_le_incl in GT.
        eapply call_returns_if_not_continues in GT; eauto.
        2: { eapply call_nval_at; eauto. done. }
        2: { intros NVAL. apply NFIT.
             destruct NVAL as (?&EXPR&?).
             do 2 red in EXPR. rewrite tc_helper in EXPR.
             rewrite EE in EXPR. inversion_clear EXPR.
             eapply fill_not_val; eauto. }
        destruct GT as (k & r & ck & RANGE & KTH & RETk).
        rewrite ic_helper.
        exists k, r, ck. split; eauto. lia.
    -
      
      apply Classical_Prop.imply_to_and in NFIT as [LONG NORET].
      destruct NORET. red.
      clear CALL. 
      intros j K PREV CALL.
      destruct (trace_take_fwd n extr !! j) eqn:JJ; rewrite JJ /= // in CALL.
      pose proof (trace_take_fwd_length_bound n extr). 
      (* apply trace_take_fwd_lookup_Some in JJ. *)
      red in MAIN. eapply MAIN in PREV.
      2: { apply trace_take_fwd_lookup_Some in JJ. rewrite JJ. eauto. }
      destruct PREV as (r&PREV'&RET).
      exists r. split; [done| ]. 
      destruct (extr S!! r) eqn:RTH; [| done]. 
      eapply (trace_take_fwd_lookup_Some' _ n) in RTH; eauto.
      2: { lia. }
      by rewrite RTH.
  Qed.

  Let OP := LocaleOP (OPRE := OPP_WF) (Locale := locale heap_lang). 
  Existing Instance OP.
  Let OM := ObligationsModel.

  Let M := AM2M ObligationsAM.
  Let ASEM := ObligationsASEM.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} _ _ => ⌜ True ⌝%I).

  Definition obls_om_traces_match_wfree: extrace heap_lang -> trace (mstate M) (mlabel M) -> Prop :=
    obls_om_traces_match_gen obls_st_rel_wfree.

  Lemma obls_st_rel_wfree_empty σ (s: mstate OM)
    (INIT: obls_is_init_st ([], σ) s):
    obls_st_rel_wfree ([], σ) s.
  Proof using.
    red. 
    rewrite /obls_st_rel /no_extra_obls.
    rewrite /obls_fairness_preservation.om_live_tids /has_obls.
    simpl in INIT. red in INIT.
    rewrite /locales_of_cfg in INIT. rewrite list_to_set_nil in INIT.
    apply proj1, eq_sym, dom_empty_inv_L in INIT.
    rewrite INIT.
    split; try set_solver.
  Qed.    

  Lemma int_ref_int_empty m ai σ s
    (FITS : fits_inf_call ic m ai {tr[ ([], σ) ]})
    (PROP : obls_st_rel_wfree ([], σ) s):
    int_ref_inf (obls_sim_rel_wfree) ⟨ ([], σ) ⟩ ⟨ s ⟩.
  Proof using. 
    apply int_ref_int_singleton.
    repeat split; try by apply PROP.
    red. simpl. intros _ TI0.
    assert (tctx_index ic = 0) by lia.
    destruct FITS as [CALL _ _ _].
    rewrite H /= in CALL.
    rewrite /call_at /= in CALL.
    by edestruct no_expr_in_empty_pool.
  Qed.    

  From trillium.program_logic Require Import simulation_adequacy_em_cond.

  Theorem om_simulation_adequacy_model_trace_multiple_waitfree Σ
        `{hPre: @heapGpreS Σ M EM} (s: stuckness) f
        (es: list (expr heap_lang)) σ1 (s1: mstate M) p
        (* s' ic *)
        m ai
        (INIT: em_is_init_st (es, σ1) s1 (ExecutionModel := EM))
        (extr : extrace heap_lang)
        (Hvex : extrace_valid extr)
        (Hexfirst : trfirst extr = (es, σ1))
    :
    PR_premise_multiple (obls_sim_rel_wfree ) (fits_inf_call ic m ai) Σ s f es σ1 s1 (p: @em_init_param _ _ EM) ->
    (∃ omtr, obls_om_traces_match_wfree extr omtr ∧ trfirst omtr = s1 /\
              int_ref_inf (obls_sim_rel_wfree) extr omtr
    ) \/
    (exists k, ¬ (fits_inf_call ic m ai) (trace_take_fwd k extr)).
  Proof using.

    (* Set Printing Implicit. *)
    intros PREM.

    destruct (decide (1 <= length es)).
    2: { clear PREM.
         
      (* TODO: make a lemma *)
         assert (length es = 0) by lia.
         assert (es = []) as -> by (destruct es; simpl in H; lia || done).
         opose proof * extrace_valid_empty as ->; eauto.

         destruct (decide (fits_inf_call ic m ai ({tr[ ([], σ1) ]}))) as [FITS | ].
         2: { right. exists 0. by rewrite trace_take_fwd_0_first. }
         
         assert (obls_st_rel_wfree ([], σ1) s1) as PROP by (by apply obls_st_rel_wfree_empty).

         left. exists (tr_singl s1).
         clear s. 
         split.
         2: { split; [done| ]. by eapply int_ref_int_empty. }
         red. by apply trace_match_singl. }

    unshelve epose proof (@PR_strong_simulation_adequacy_traces_multiple _ _ EM 
                            HeapLangEM (obls_sim_rel_wfree) (fits_inf_call ic m ai)
                            _ _ _ _ _ 
                            s f es σ1 s1 p
                extr
                Hvex
                ltac:(done)
                obls_ves_wrapper
                (obls_st_rel_wfree)
                (fun oτ '(_, τ') => oτ = τ')
                _ _ _ _ _ _ _
                PREM
      ) as SIM.
    { apply fits_inf_call_prev. }
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

End Lib.

Lemma fair_call_extend etr Ki Kj τ i j ci
  (FAIR: fair_call etr (TpoolCtx Ki τ) i)
  (LE: j <= i)
  (ITH: etr S!! i = Some ci)
  (NSTUCKi: locale_enabled_safe τ ci)
  (NORET: ¬ has_return etr (TraceCtx i (TpoolCtx Ki τ))):
  fair_call etr (TpoolCtx Kj τ) j.
Proof using.
  red. intros k ck LEjk KTH ENk NORETk.
  red in FAIR. ospecialize * (FAIR (max i k) (if (decide (i <= k)) then ck else ci)).
  { lia. }
  { destruct decide; [rewrite -KTH| rewrite -ITH]; f_equal; lia. }
  { destruct decide; done. }
  { red. intros (r & DOMr & RETr).
    destruct NORET. red. eauto. }
  destruct FAIR as [d FAIR].
  rewrite Nat.max_comm in FAIR. 
  pose proof (max_plus_consume k i d) as [d' EQ]. rewrite EQ in FAIR.
  eauto.
Qed.


Lemma find_main_call etr i K τ m a ci
  (tpc := TpoolCtx K τ)
  (VALID : extrace_valid etr)
  (FAIR : fair_call etr tpc i)
  (ITH : etr S!! i = Some ci)
  (CALL : call_at tpc ci m a (APP := App))
  (M_FUN: exists f x b, m = RecV f x b)
  (NORET: ¬ has_return etr (TraceCtx i tpc))
  :
  exists i' K' a' ci',
    let tpc' := TpoolCtx K' τ in
    fair_call etr tpc' i' /\ etr S!! i' = Some ci' /\ call_at tpc' ci' m a' (APP := App) /\
    previous_calls_return_tr etr i' τ m /\
    i' <= i /\
      (* nval_at tpc' ci /\ *)
      no_return_before etr tpc' i' i.
Proof using.
  subst tpc.
  assert (exists j cj Kj aj, fair_call etr {| tpctx_ctx := Kj; tpctx_tid := τ |} j /\ etr S!! j = Some cj /\ call_at {| tpctx_ctx := Kj; tpctx_tid := τ |} cj m aj (APP := App) /\ j ≤ i ∧
    (* nval_at {| tpctx_ctx := Kj; tpctx_tid := τ |} ci /\ *)
    no_return_before etr {| tpctx_ctx := Kj; tpctx_tid := τ |} j i /\
    ¬ has_return etr (TraceCtx j {| tpctx_ctx := Kj; tpctx_tid := τ |})) as [j JJ].
  { do 4 eexists. repeat split; eauto.
    red. intros (k & ? & (?&?&?&?&?)).
    assert (k = i) as -> by lia.
    rewrite ITH in H1. inversion H1. subst x0. 
    eapply not_return_nval; eauto.
    eapply call_nval_at; eauto. done. }

  clear FAIR NORET CALL K a.
  
  revert JJ. pattern j. apply lt_wf_ind; clear j.
  intros j IH. intros (cj&Kj&aj&FAIRj&JTH&CALLj&LEji& NVALj &NORETj).
  destruct (Classical_Prop.classic (previous_calls_return_tr etr j τ m)) as [| NESTED].
  { exists j. do 3 eexists. simpl. repeat split; eauto.
    by rewrite CALLj. }

  rewrite /previous_calls_return_tr in NESTED.
  apply not_forall_exists_not in NESTED as (k & X). 
  apply not_forall_exists_not in X as (Kk & X).
  apply Classical_Prop.imply_to_and in X as [LTkj X]. 
  apply Classical_Prop.imply_to_and in X as [CALL' X].

  pose proof JTH as KTH. eapply mk_is_Some, state_lookup_prev in KTH as [ck KTH].
  2: { apply Nat.lt_le_incl, LTkj. }
  rewrite KTH /= in CALL'. destruct CALL' as [ak CALLk].

  ospecialize (IH k _ _).
  { lia. }
  2: done.
  
  assert (nval_at {| tpctx_ctx := Kk; tpctx_tid := τ |} cj) as NVALkj.
  { edestruct decide as [NVAL | NNVAL]; [| by apply NVAL| ].
    { apply _. }
    eapply (call_returns_if_not_continues _ k j) in NNVAL; eauto.
    3: lia.
    2: { eapply call_nval_at; eauto. done. }
    destruct NNVAL as (r&?&?&DOMr&RTH&RETr).
    destruct X. exists r. split; [lia| ].
    rewrite RTH /=. eauto.
    rewrite RETr. eauto. }

  destruct M_FUN as (?&?&?&->).
  destruct NVALkj as (ek & KJ & NVALkj). 
  opose proof * (call_ctx_is_deeper x x0 x1 Kk ek Kj aj) as [K' ->]. 
  { red in KJ. simpl in KJ. 
    apply Some_inj.
    rewrite -KJ.
    do 2 red in CALLj. simpl in CALLj.
    by rewrite -CALLj. }
  { done. }
  
  do 3 eexists. repeat split; eauto. 
  2: { lia. }
  2: { edestruct decide as [NVAL | NNVAL]; [| by apply NVAL| ].
       { apply _. }

       rewrite /no_return_before in NNVAL.
       apply NNP_P in NNVAL.

       (* TODO: ? make a lemma, use below  *)
       
       destruct NNVAL as (r & ? & v & cr & LEkr & RTH & RETr).
       destruct (decide (r <= j)).
       - destruct X. exists r. split.
         { split; try lia.
           destruct (decide (k = r)) as [<- | ?]; [| lia].
           set_solver. }
         rewrite RTH /=.
         rewrite RETr. eauto.
       - opose proof * (nested_call_returns_earlier _ _ _ _ τ Kk _ ck k _ _ cj) as RETj; eauto.
         { lia. }
         { lia. }
         destruct RETj as (rj & ? & ? & ?&?&?&RETj).
         destruct NORETj. red.
         exists rj. red. eauto. }
  { eapply (fair_call_extend _ _ _ _ j k); eauto.
    { lia. }
    red. rewrite /exec_traces.locale_enabled /not_stuck_tid.
    split.
    - rewrite CALLj /=. 
      eexists. split; eauto.
      by apply fill_not_val. 
    - eapply RecV_App_not_stuck in CALLj; eauto.
      by apply under_ctx_spec. }

  intros (r & v & cr & LEkr & RTH & RETr).
  destruct (decide (r <= j)).
  - destruct X. exists r. split.
    { split; try lia.
      destruct (decide (k = r)) as [<- | ?]; [| lia].
      set_solver. }
    rewrite RTH /=.
    rewrite RETr. eauto.
  - opose proof * (nested_call_returns_earlier _ _ _ _ τ Kk _ ck k _ _ cj) as RETj; eauto.
    { lia. }
    { lia. }
    destruct RETj as (rj & ? & ? & ?&?&?&RETj).
    destruct NORETj. red.
    exists rj. red. eauto.  
Qed.

Definition always_returns_main s P τ m tr :=
  forall i K a ci, 
      let tpc := TpoolCtx K τ in
      let tc := TraceCtx i tpc in
      fair_call tr tpc i ->
      tr S!! i = Some ci ->
      previous_calls_return_tr tr i (tpctx_tid tpc) m ->
      call_at tpc ci m a (APP := App) ->
      P a ->
      has_return tr tc \/ s = MaybeStuck /\ gets_stuck_ae tr tc.

(** This is the culprit of why we don't actually use non-trivial argument predicate P.
    The call argument at index i satisfying P doesn't imply the same for argument at a previous call at some index j.
    However in fact, this reduction is only really needed for proving restricted wait-freedom, and the corresponding case studies we consider do not restrict their argument.
    So in theory it might be possible to allow argument restriction for full wait-freedom and avoid it for restricted wait-freedom. *)
Lemma main_returns_reduction s' m τ etr
  (VALID: extrace_valid etr)
  (M_FUN: exists f x b, m = RecV f x b):
  always_returns_main s' any_arg τ m etr -> always_returns m s' any_arg τ etr.
Proof using.
  rewrite /always_returns_main /always_returns. 
  intros MAIN_RET. intros i K a ci FAIR ITH CALL _.

  odestruct (@Classical_Prop.classic _) as [RET | NORET]; [by apply RET| ].
  apply Classical_Prop.not_or_and in NORET as (NORET & ?). 
  
  opose proof * find_main_call as X; eauto.

  destruct X as (j & K' & a' & c' & ?&?&?&?&PREV&NVALj).
  ospecialize * (MAIN_RET j K').
  1-4: by eauto.
  { done. }

  destruct MAIN_RET as [RETj | [-> STUCKj]].
  2: { right. split; [done| ].
       (* TODO: extract a lemma *)
       red. intros.
       red in STUCKj. odestruct (STUCKj (max i N) _) as (?&?&?&?).
       { pose proof (Nat.max_spec_le i N) as [[? MAX] | [? MAX]]; rewrite MAX; eauto. }
       exists x. repeat split; eauto.
       { lia. }
       red. red in H7. destruct H7 as (?&?&?&?).
       eexists. repeat split; eauto.
       lia. }

  destruct RETj as (r & v & cr & LEjr & RTH & RETr).
  assert (i <= r) as LEir.
  { destruct (Nat.lt_ge_cases r i) as [LT | LEri]; [| done].
    destruct NVALj. exists r. split; [lia| ].
    red. do 2 eexists. eauto. }

  destruct M_FUN as (?&?&?&->).
  eapply no_return_before_equiv_nvals with (j := i) in NVALj; eauto.
  2: { red. rewrite /expr_at. rewrite H2. eauto. }
  rewrite ITH /= in NVALj. -
  
  destruct NVALj as (ej & JJ & NVALj). 
  opose proof * (call_ctx_is_deeper x x0 x1 K' ej K a) as [K_ ->]. 
  { red in JJ. simpl in JJ. 
    apply Some_inj.
    rewrite -JJ.
    do 2 red in CALL. simpl in CALL.
    by rewrite -CALL. }
  { done. }

  opose proof * (nested_call_returns_earlier _ _ _ _ τ K' _ c' j _ _ ci) as RETj; eauto.
  destruct RETj as (rj & ? & ? & ?&?&?&RETj).
  destruct NORET. red.
  exists rj. red. eauto.
Qed.


Lemma has_return_fin_trace etr tpc i
  (FAIR : fair_call etr tpc i)
  (len : nat)
  (LEN : trace_len_is etr (my_omega.NOnum len))
  (c : list expr * trillium.program_logic.language.state heap_lang)
  (LAST : etr S!! (len - 1) = Some c)
  (DOM : i ≤ len - 1)
  (NS : not_stuck_tid (tpctx_tid tpc) c)
  (NORET : ¬ has_return etr {| tctx_index := i; tctx_tpctx := tpc |})
  (e : expr)
  (EE : from_locale c.1 (tpctx_tid tpc) = Some e)
  (NVAL : nval_at tpc c)
  :
  has_return etr {| tctx_index := i; tctx_tpctx := tpc |}.
Proof using.
  red in FAIR. destruct tpc as [K τ]. 
  ospecialize (FAIR (len - 1)).
  
  assert (locale_enabled τ c) as EN. 
  { red. eexists. split; eauto.
    (* TODO: make lemma, use above *)
    destruct NVAL as (?&EXPR&?).
    red in EXPR. simpl in *. 
    rewrite EE in EXPR. inversion_clear EXPR.
    eapply fill_not_val; eauto. }
  
  assert (locale_enabled_safe τ c) as EN'. 
  { split; auto. }
  
  rewrite LAST /= in FAIR. ospecialize (FAIR _ _ _ _ _); eauto.
  { intros (?&?&(?&?&?&?&?)).
    destruct NORET. red. eexists. esplit; eauto. }
  
  destruct FAIR as (k & ? & NEXT & FAIR).
  red in FAIR. destruct FAIR as [DIS | (? & LBL & STEP)].
  2: { eapply mk_is_Some, label_lookup_dom in LBL; eauto.
       simpl in *. lia. }
  destruct k.
  { rewrite Nat.add_0_r in NEXT. rewrite LAST in NEXT.
    inversion NEXT. set_solver. }
  eapply mk_is_Some, state_lookup_dom in NEXT; eauto.
  simpl in *. lia.
Qed.
