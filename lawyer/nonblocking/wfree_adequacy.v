From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From trillium.program_logic Require Import execution_model weakestpre adequacy simulation_adequacy_em_cond. 
From trillium.prelude Require Import classical.
From fairness Require Import fairness locales_helpers utils.
From lawyer Require Import program_logic sub_action_em action_model.
From lawyer.examples Require Import orders_lib obls_tactics.
From lawyer.nonblocking Require Import trace_context om_wfree_inst mk_ref pr_wfree wfree_traces wptp_gen pwp.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination.
From heap_lang Require Import lang simulation_adequacy.


Close Scope Z.

Section CallInTrace.
  Context (tr: extrace heap_lang).
  Context (m: val). (** the method under consideration *)
  
  Definition has_return '(TraceCtx i tpc as tc) :=
    exists j r cj, i <= j /\ tr S!! j = Some cj /\ return_at tpc cj r.

  Definition always_returns :=    
    forall tc a ci, let '(TraceCtx i tpc) := tc in
      fair_ex (tpctx_tid tpc) tr ->
      tr S!! i = Some ci ->
      call_at tpc ci m a (APP := App) ->
      has_return tc.
  
End CallInTrace.


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
  Let ii := tctx_index ic.
  Let tc := tctx_tpctx ic. 
  Let Ki := tpctx_ctx tc.
  Let τi := tpctx_tid tc. 
  Context (m ai: val).

  Definition no_extra_obls (_: cfg heap_lang) (δ: mstate M) :=
    forall τ', default ∅ (ps_obls δ !! τ') ≠ ∅ -> τ' = τi.

  Definition obls_sim_rel_wfree extr omtr :=
    obls_sim_rel extr omtr /\ no_extra_obls (trace_last extr) (trace_last omtr).

  (* Definition wfree_trace_inv `{Hinv : @IEMGS _ _ HeapLangEM EM Σ} *)
  (*   (extr: execution_trace heap_lang) (omtr: auxiliary_trace M): iProp Σ := *)
  (*   ⌜ no_extra_obls (trace_last extr) (trace_last omtr) ⌝. *)

  Let fic := fits_inf_call ic m ai.

  (* TODO: move *)
  Instance fic_dec: ∀ etr, Decision (fits_inf_call ic m ai etr).
  Proof using.
    intros. rewrite /fits_inf_call.
    apply and_dec.
    { destruct (etr !! (tctx_index ic)); solve_decision. }
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

  (* TODO: move, remove duplicate *)
  Lemma fic_fpc: filter_pref_closed (fits_inf_call ic m ai).
  Proof using.
    red. apply fits_inf_call_prev. 
  Qed.

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
    PR_premise_multiple obls_sim_rel_wfree (fits_inf_call ic m ai) Σ s es σ1 s1 (p: @em_init_param _ _ EM) ->
    (∃ omtr, obls_om_traces_match_wfree extr omtr ∧ trfirst omtr = s1) \/
    (exists k, ¬ (fits_inf_call ic m ai) (trace_take_fwd k extr)).
  Proof using.
    intros PREM.

    unshelve epose proof (@PR_strong_simulation_adequacy_traces_multiple _ _ EM 
                            HeapLangEM obls_sim_rel_wfree (fits_inf_call ic m ai)
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

  Open Scope WFR_scope. 

  Context (SPEC: WaitFreeSpec m).
  Let F := wfs_F _ SPEC.

  Definition init_om_wfree_state
    (* (F: nat) (TI: nat) (d0 d1: Degree) (τi: locale Λ) (l0: Level) (ii: nat) *)
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
      2: { pose proof (flatten_gset_map_img_gtg_empty (locales_of_cfg c)) as D. simpl in D. rewrite D.
        done. }
      rewrite map_img_insert_L.
      rewrite -gset_to_gmap_difference_singleton.
      rewrite flatten_gset_union.
      pose proof (flatten_gset_map_img_gtg_empty (locales_of_cfg c ∖ {[τi]})) as D. simpl in D. rewrite D.
      rewrite flatten_gset_singleton. set_solver.
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
    (NOOBS': pr_wfree.no_extra_obls ic c δ)
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

  From iris.algebra Require Import auth gmap gset excl gmultiset big_op mono_nat gmap_view.

  (* TODO: move *)
  Lemma gmap_insert_delete_union `{Countable K} {A: Type} k a (mm: gmap K A):
        <[ k := a ]> mm = {[ k := a ]} ∪ delete k mm.
  Proof using.
    apply map_eq. intros k'.
    destruct (decide (k' = k)) as [-> | ?].
    { rewrite lookup_insert.
      erewrite lookup_union_Some_l; eauto.
      by apply lookup_singleton_Some. }
    rewrite lookup_insert_ne; [| done].
    rewrite lookup_union_r.
    2: { by apply lookup_singleton_None. }
    symmetry. by apply lookup_delete_ne.
  Qed.    

  Lemma empty_obls_helper `{!ObligationsGS Σ} (T: gset (locale heap_lang)):
  @own Σ _
           (@obls_pre_obls _ _ _ _ OP _ _)
           (@obls_obls _ _ _ _ OP _ _)
           (◯ (Excl <$> @gset_to_gmap nat _ _ _ ∅ T)) -∗
  [∗ set] τ ∈ T, obls τ ∅.
  Proof using.
    iIntros "OB".
    rewrite fmap_gset_to_gmap.
    rewrite -gmap.big_opS_gset_to_gmap_L.
    rewrite big_opS_auth_frag.
    destruct (decide (T = ∅)).
    { rewrite e. set_solver. }
    rewrite big_opS_own; [| done].
    iApply (big_sepS_impl with "OB").
    iModIntro. set_solver.
  Qed.

  (** for simplicity, we forget about the specific phases *)
  Lemma init_wfree_resources_weak `{!ObligationsGS Σ} c:
    obls_init_resource (init_om_wfree_state c) () -∗
    (cp_mul π0 d0 (2 * F) ∗ cp_mul π0 d0 ii ∗ cp π0 d1) ∗
    (⌜ τi ∈ locales_of_cfg c ⌝ →
     ∃ s, obls τi {[ s ]} ∗ sgn s l0 (Some false) ∗ ep s π0 d0) ∗
    ([∗ set] τ ∈ locales_of_cfg c ∖ {[ τi ]}, obls τ ∅) ∗
    ([∗ set] τ ∈ locales_of_cfg c, ∃ π, th_phase_eq τ π).  
    (* closed_pre_helper {Σ: gFunctors} {oGS: ObligationsGS Σ} *)
    (*       (e: expr) (k: nat) (d: Degree) (σ: state) (b: nat): *)
    (* obls_init_resource (init_om_state ([e], σ) (k *: {[+ d +]}) b) ()  ⊢ *)
    (*   th_phase_eq (locale_of [] e) (ext_phase π0 0)  ∗ *)
    (*   cp_mul (ext_phase π0 0) d k ∗ obls (locale_of [] e) ∅. *)
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
      rewrite -gmap_disj_op_union.
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
  Lemma wptp_from_gen_nil {Σ : gFunctors}
    (W: expr → locale heap_lang → (val → iPropI Σ) → iProp Σ)
    tp0:
    ⊢ wptp_from_gen W tp0 [] [].
  Proof using. clear. rewrite /wptp_from_gen. set_solver. Qed.

  Lemma init_pwp `{!irisG heap_lang LoopingModel Σ} τ e0:
    ⊢ pwp.pwp MaybeStuck ⊤ τ (subst "m" m e0) (λ _, True).
  Proof using.
    (* should follow from FTLR and specification for m.
       Need to assume/derive logrel for m (besides its Lawyer spec)
     *)
  Admitted.

  Lemma init_wptp_wfree_pwps `{Hinv: @IEMGS _ _ HeapLangEM EM Σ} tp0 tp N
    (NO: τi ∉ locales_of_list_from tp0 tp)
    (SUBST: Forall (λ e, ∃ e0, e = subst "m" m e0) tp):
  ⊢ wptp_from_gen (thread_pr ic MaybeStuck N) tp0 tp
      (map (λ (_ : nat) (_ : val), ⌜ True ⌝%I)
         (adequacy_utils.locales_of_list_from tp0 tp)).
  Proof using.
    iInduction tp as [|e tp] "IH" forall (tp0 NO).
    { simpl. iApply wptp_from_gen_nil. }
    rewrite adequacy_utils.locales_of_list_from_cons. 
    rewrite map_cons. iApply wptp_from_gen_cons. iSplitR.
    2: { simpl. iApply "IH".
         - iPureIntro. by inversion SUBST. 
         - iPureIntro. set_solver. }
    rewrite /thread_pr. rewrite decide_False.
    2: { intros EQ. apply NO. rewrite locales_of_list_from_locales.
         rewrite /τi EQ. set_solver. }
    inversion SUBST as [| ?? [? ->]]. subst. 
    iApply init_pwp.
  Qed.

  Definition tpool_init_restr (tp: list expr) :=
    Forall (fun e => exists e0, e = subst "m" m e0) tp /\
    (ii = 0 -> exists e, from_locale tp τi = Some e /\ under_ctx Ki e = Some (m ai)) /\
    (forall e, from_locale tp τi = Some e -> to_val e = None). 

  Lemma init_wptp_wfree `{Hinv: @IEMGS _ _ HeapLangEM EM Σ} c
    (ETR0: tpool_init_restr c.1):
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    (⌜ ii = 0 ⌝ → ∃ π, cp_mul π0 d0 F ∗ th_phase_frag τi π (/2)%Qp) -∗
    wptp_wfree ic MaybeStuck {tr[ c ]}
      (map (λ _ _, True) (adequacy_utils.locales_of_list c.1)).
  Proof using.
    simpl. iIntros "T".
    rewrite /wptp_wfree. simpl. 
    destruct (thread_pool_split c.1 τi) as (tp1 & tp2 & tp' & EQ & TP' & NO1 & NO2).
    rewrite EQ. rewrite !locales_of_list_from_app'. rewrite !map_app /=.
    destruct ETR0 as (TP & II0 & NVAL0).
    rewrite EQ in TP.
    iApply wptp_from_gen_app. iSplitR.
    { iApply init_wptp_wfree_pwps.
      - done. 
      - by apply Forall_app, proj1 in TP. }
    simpl. iApply wptp_from_gen_app. iSplitL.
    2: { iApply init_wptp_wfree_pwps.
         - done. 
         - by do 2 (apply Forall_app, proj2 in TP). }

    destruct TP' as [-> | (e & -> & LOC)].
    { simpl. iApply wptp_from_gen_nil. }
    simpl. iApply wptp_gen_singleton.
    rewrite /thread_pr. rewrite decide_True; [| done].
    rewrite /wp_tc.
    destruct ii eqn:TI.
    2: { rewrite leb_correct; [| lia].
         apply Forall_app, proj2 in TP.
         apply Forall_app, proj1 in TP.
         inversion TP as [| ?? [? ->]]. subst.
         iApply init_pwp. }
    rewrite leb_correct_conv; [| lia].
    iDestruct ("T" with "[//]") as (π) "[CPS PH]".
    rewrite half_inv2. 
    iPoseProof (get_call_wp _ SPEC ai with "[$] [$]") as "WP".
    destruct (II0 eq_refl) as (e_ & IN & CTX).
    rewrite LOC EQ /= in IN.
    rewrite /from_locale in IN. rewrite from_locale_from_locale_of in IN.
    inversion IN. subst e_.
    rewrite CTX. simpl.
    iApply (wp_stuck_mono with "[$]"). done.
  Qed.

  (* TODO: move, use in other places *)
  Lemma elem_of_locales_of_list_from_from_locale_from tp0 τ tp:
    τ ∈ locales_of_list_from tp0 tp <-> exists e, from_locale_from tp0 tp τ = Some e.
  Proof using.
    clear. 
    rewrite locales_of_list_from_locales.
    rewrite elem_of_list_In in_map_iff.
    rewrite ex_prod. rewrite ex2_comm.
    apply exist_proper. intros e.
    rewrite from_locale_from_lookup.
    rewrite /locale_of.
    setoid_rewrite <- elem_of_list_In.
    setoid_rewrite elem_of_list_lookup.  
    split.
    - intros (pf & <- & (i & IN)).
      pose proof IN as ?%prefixes_lookup_orig.
      pose proof IN as ?%prefixes_from_ith_length. simpl in *.
      split; [| lia]. rewrite -H. f_equal. lia.
    - intros (IN & LEN).
      eexists. split.
      2: { eexists. eapply prefixes_from_lookup; eauto. }
      rewrite length_app.
      apply lookup_lt_Some in IN. simpl in *. 
      rewrite firstn_length_le; lia.
  Qed.

  (* (* TODO: move *) *)
  Lemma from_locale_from_elem_of tp0 tp τ e
    (IN: from_locale_from tp0 tp τ = Some e):
    e ∈ tp.
  Proof using.
    apply from_locale_from_lookup in IN.
    destruct IN as [IN _].
    eapply elem_of_list_lookup; eauto.
  Qed.    

  Lemma tp_init_in tp τ
    (IN: τ ∈ locales_of_list tp)
    (ETR0: tpool_init_restr tp):
    exists e0, from_locale tp τ = Some (subst "m" m e0).
  Proof using.
    destruct ETR0 as [TP _].
    apply elem_of_locales_of_list_from_from_locale_from in IN as (e & IN).
    rewrite /from_locale IN.
    apply Forall_forall with (x := e) in TP; [set_solver| ].
    eapply from_locale_from_elem_of; eauto.
  Qed.

  Lemma PR_premise_wfree `{hPre: @heapGpreS Σ M EM} c
    (ETR0: tpool_init_restr c.1)
    :
  PR_premise_multiple obls_sim_rel_wfree (fits_inf_call ic m ai)
    Σ MaybeStuck c.1 c.2
    (init_om_wfree_state c) ((): @em_init_param _ _ EM).
  Proof using.    
    red. iIntros (Hinv) "(PHYS & MOD)". simpl.
    iModIntro.
    iExists (wfree_trace_inv ic).
    
    iExists (PR_wfree ic SPEC ai). simpl. 

    do 2 rewrite bi.sep_assoc. iSplitL.
    2: { rewrite /adequacy_cond.rel_always_holds_with_trace_inv.

         iIntros (extr omtr [tp σ] EXTRA FIN NSTUCK).
         simpl. iIntros "(%VALID_STEP & HEAP & MSI & [%TH_OWN %OBLS]) POSTS #INV".
         red in EXTRA. destruct EXTRA as (VALID & EX0 & OM0 & CONT_SIM). 
         iApply fupd_mask_intro_discard; [done| ].

         rewrite /wfree_trace_inv. iDestruct "INV" as %(NOOBS' & NVAL).
         rewrite /obls_sim_rel_wfree. iSplit; [| done].

         destruct extr.
         { iPureIntro.
           simpl in VALID_STEP.
           inversion VALID. subst.
           red in EX0, OM0. simpl in EX0, OM0. subst.
           rewrite /obls_sim_rel_wfree /obls_sim_rel /obls_sim_rel_gen.
           simpl.

           split; [done| ]. simpl. red.
           red. simpl. eapply @obls_τi_enabled; eauto. }
         
         simpl in VALID_STEP. inversion VALID. subst. simpl in *.
         (* red in EX_FIN. simpl in EX_FIN. subst. simpl. *)
         rewrite /obls_sim_rel. iSplit.
         { simpl. iPureIntro. 
           destruct a. done. }
         simpl. rewrite /obls_st_rel.

         iPureIntro.
         red. simpl.
         eapply @obls_τi_enabled; eauto. }

    rewrite -surjective_pairing. 
    iSplitL.
    2: { rewrite /wfree_trace_inv. iPureIntro. split.
         - simpl. red. rewrite /init_om_wfree_state. simpl.
           intros τ NEMPTY. destruct decide.
           2: { rewrite lookup_gset_to_gmap option_guard_decide in NEMPTY.
                destruct decide; simpl in NEMPTY; done. }
           destruct lookup eqn:L; try done. 
           apply lookup_insert_Some in L. destruct L as [| [? L]]; [set_solver| ].
           apply lookup_gset_to_gmap_Some in L. set_solver.
         - simpl.
           destruct (from_locale c.1 τi) eqn:IN; rewrite IN; [| done].
           destruct ETR0 as (_&_&NVAL0).
           by apply NVAL0 in IN. }
    
    iSplitR.
    { simpl. iApply hl_config_wp. }
    rewrite /pr_pr_wfree. simpl.

    iDestruct (init_wfree_resources_weak with "[$]") as "(CPS & OB' & OBLS & PHS)".
    iFrame.
    rewrite -{2}(difference_union_intersection_L (locales_of_cfg c) {[ τi ]}).    
    rewrite big_sepS_union.
    2: { set_solver. }
    iDestruct "PHS" as "[$ PH]".
    #[local] Arguments Nat.leb _ _ : simpl nomatch.    
    rewrite /extra_fuel. simpl.
    iDestruct "CPS" as "(CPS_PRE & CPS0 & CP1)".
    iDestruct (cp_mul_split with "CPS_PRE") as "[CPS_PRE CPS_PRE']". rewrite Nat.add_0_r.
    rewrite Nat.sub_0_r. fold ii.
    rewrite bi.sep_comm. rewrite -bi.sep_assoc. iSplitL "CPS0 CPS_PRE".
    { destruct leb; [| done]. iFrame. }
    rewrite /obls_τi'.

    rewrite -bi.sep_assoc. 
    iAssert (_%I ∗ (⌜ ii = 0 ⌝ →
                    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
                    ∃ π, th_phase_frag τi π (/ 2)%Qp))%I with "[PH]" as "[X PHτi]".
    2: iSplitL "X"; [by iApply "X"| ].
    { destruct (decide (τi ∈ locales_of_cfg c)).
      2: { iSplitL.
           - by iIntros (?).
           - iIntros (II0). destruct ETR0 as (?&IN&?).
             destruct (IN II0) as (?&E&?). destruct n.
             eapply locales_of_cfg_Some; eauto.
             Unshelve. apply c. }
      rewrite intersection_comm_L subseteq_intersection_1_L.
      2: set_solver.
      rewrite big_sepS_singleton.
      fold τi.
      destruct ii eqn:II.
      - rewrite leb_correct_conv; [| lia].
        setoid_rewrite th_phase_frag_halve at 1. iDestruct "PH" as (?) "(PH&?)".
        rewrite half_inv2. 
        iSplitL "PH"; iIntros (?); iExists _; iFrame.
      - iSplitL.
        2: { iIntros (?). lia. }
        iIntros (?). iFrame. }

    iSplitR "PHτi CPS_PRE'".
    { destruct decide.
      - iSpecialize ("OB'" with "[//]"). iFrame.
      - iFrame. }

    iApply init_wptp_wfree; [done| ].
    iFrame. 
  Qed. 

  Definition wfreeΣ: gFunctors.
  Admitted.

  Instance wfree_pre: @heapGpreS wfreeΣ M EM.
  Admitted. 

  Local Lemma ic_helper:
    tctx_tpctx ic = {| tpctx_ctx := Ki; tpctx_tid := τi |}.
  Proof using. clear. by destruct ic as [? []]. Qed.

  Theorem simple_om_simulation_adequacy_terminate_multiple_waitfree extr
        (ETR0: exists e0, (trfirst extr).1 = [subst "m" m e0])
    :
    extrace_valid extr -> 
    fair_ex τi extr ->
    terminating_trace extr \/ 
    exists k, ¬ fits_inf_call ic m ai (trace_take_fwd k extr).
  Proof.
    intros VALID FAIR.
    destruct ETR0 as [e0 ETR0]. 

    destruct (@decide (ii = 0 → ∃ e,
                    from_locale (trfirst extr).1 τi = Some e ∧ under_ctx Ki e = Some (m ai))) as [II0| ].
    { apply impl_dec; [apply _| ].
      (* TODO: make a lemma + definition *)
      apply ex_fin_dec with
             (l := from_option (flip cons nil) [] (from_locale (trfirst extr).1 τi)).
      { solve_decision. }
      intros ? (RUNS & ?).
      simpl. rewrite RUNS. simpl. tauto. }
    2: { apply Classical_Prop.imply_to_and in n as (II & NO0).
         right. exists 0. intros FITS. apply NO0.
         red in FITS. apply proj1 in FITS.
         fold ii in FITS.
         rewrite trace_take_fwd_0_first in FITS.
         rewrite II /= in FITS.
         red in FITS. simpl in FITS. eauto.
         red in FITS. rewrite ic_helper in FITS.
         eexists. split; eauto. by rewrite under_ctx_fill. }
    destruct (@decide (∀ e, from_locale (trfirst extr).1 τi = Some e → to_val e = None)) as [E0| ].
    { destruct (from_locale (trfirst extr).1 τi) eqn:E.
      2: { left. set_solver. }
      destruct (to_val e) eqn:V.
      { right. set_solver. }
      left. set_solver. }
    2: { apply not_forall_exists_not in n as [e VAL].
         apply Classical_Prop.imply_to_and in VAL as [E VAL].
         right. exists 0. intros FITS. apply VAL.
         red in FITS. do 2 apply proj2 in FITS.
         specialize (FITS 0). rewrite trace_take_fwd_0_first /= in FITS.
         rewrite E in FITS. done. }

    opose proof (om_simulation_adequacy_model_trace_multiple_waitfree
                wfreeΣ _ (trfirst extr).1 _ _ _ _ _ VALID _ _ _) as ADEQ.
    { apply init_om_wfree_is_init. }
    { apply surjective_pairing. }
    { rewrite ETR0. simpl. lia. } 
    { rewrite -surjective_pairing. 
      eapply PR_premise_wfree; eauto.

      split; [| split].
      - (* TODO: can generalize to more than 1 initial thread *)
        rewrite ETR0. constructor; [| done]. eauto.
      - eauto.
      - eauto. }
    
    destruct ADEQ as [(mtr & MATCH & OM0) | RET]. 
    2: { right. done. } 
    left. 
    opose proof (obls_matching_traces_OM _ _ _ _ MATCH _) as (omtr & MATCH'' & SR & OM_WF & FIRST'').
    { intros ?? X. apply X. }
    { eapply obls_init_wf. rewrite OM0. apply init_om_wfree_is_init. }
 
    assert (forall τ, obls_trace_fair τ omtr) as OM_FAIR.
    { intros.
      destruct (decide (τ = τi)) as [-> | NEQ].
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

  (* TODO: move *)
  Lemma ft_prepend_lookup_0 {St L: Type} (tr: finite_trace St L) s l:
    ft_prepend tr s l !! 0 = Some s.
  Proof using.
    induction tr.
    { done. }
    simpl.
    rewrite trace_lookup_extend_lt; [done| ]. 
    by apply trace_lookup_lt_Some.
  Qed.

  (* TODO: move *)
  Lemma ft_prepend_length  {St L: Type} (tr: finite_trace St L) s l:
    trace_length (ft_prepend tr s l) = S (trace_length tr).
  Proof using.
    clear dependent ic. clear dependent m. 
    generalize dependent s. generalize dependent l. induction tr.
    { simpl. lia. }
    intros. simpl. rewrite IHtr. lia.
  Qed.

  (* TODO: move *)
  Lemma ft_prepend_lookup_S {St L: Type} (tr: finite_trace St L) s l i:
    ft_prepend tr s l !! (S i) = tr !! i.
  Proof using.
    clear dependent ic. clear dependent m. 
    generalize dependent i. induction tr.
    { simpl. rewrite /lookup /trace_lookup. simpl.
      destruct i; done. }
    intros. simpl.
    
    simpl. rewrite /lookup. rewrite /trace_lookup. simpl.
    replace (trace_length (ft_prepend tr s l)) with (S (trace_length tr)).
    2: { by rewrite ft_prepend_length. } 

    destruct (decide (trace_length tr = i)). 
    - rewrite !bool_decide_true; try lia. done.
    - rewrite !bool_decide_false; try lia.
      erewrite IHtr. done.      
  Qed.

  (* TODO: move *)
  Lemma trace_take_fwd_lookup_Some (etr: extrace heap_lang) n i c
    (ITH: trace_take_fwd n etr !! i = Some c):
    etr S!! i = Some c.
  Proof using.
    generalize dependent c. generalize dependent n. generalize dependent etr.
    induction i.
    { intros [|] ??; destruct n; simpl; try done.
      rewrite state_lookup_0. simpl.
      by rewrite ft_prepend_lookup_0. } 
    intros. destruct etr.
    { destruct n; done. }
    simpl. destruct n; [done| ].
    rewrite state_lookup_cons.
    simpl in ITH.
    rewrite ft_prepend_lookup_S in ITH. eauto.
  Qed.

  (* TODO: move, use in pr_wfree? *)
  Lemma from_locale_from_app_Some tp0 tp1 tp2 τ e:
    from_locale_from tp0 (tp1 ++ tp2) τ = Some e <->
    from_locale_from tp0 tp1 τ = Some e \/ from_locale_from (tp0 ++ tp1) tp2 τ = Some e.
  Proof using.
    clear. 
    rewrite !from_locale_from_lookup.
    rewrite lookup_app. rewrite !length_app.
    destruct (tp1 !! (τ - length tp0)) eqn:L1.
    - split; try tauto. intros [? | [EQ2 LEN2]]; [done| ].
      apply lookup_lt_Some in L1, EQ2. lia.
    - etrans.
      2: { rewrite Morphisms_Prop.or_iff_morphism; [..| reflexivity].
           2: apply iff_False_helper; set_solver. 
           reflexivity. }
      rewrite False_or. rewrite Nat.sub_add_distr.
      apply iff_and_pre. intros ?%lookup_lt_Some.
      apply lookup_ge_None in L1. lia.
  Qed.

  (* TODO: move *)
  Lemma from_locale_from_Some_app' tp0 tp tp' ζ e :
    from_locale_from (tp0 ++ tp) tp' ζ = Some e ->
    from_locale_from tp0 (tp ++ tp') ζ = Some e.
  Proof.
    intros EQ. rewrite from_locale_from_app_Some. eauto. 
  Qed.

  (* (* TODO: move to Trillium, replace the original version? *) *)
  (* Lemma from_locale_from_equiv_strong tp0 tp0' tp tp' ζ : *)
  (*   locales_equiv tp0 tp0' -> *)
  (*   locales_equiv_from tp0 tp0' tp tp' -> *)
  (*   from_locale_from tp0 tp ζ = from_locale_from tp0' tp' ζ. *)
  (* Proof. *)
  (*   revert tp0 tp0' tp'. induction tp as [|e tp IH]; intros tp0 tp0' tp' Heq0 Heq. *)
  (*   { destruct tp' as [|e' tp']; try by apply Forall2_length in Heq. } *)
  (*   simpl in *. *)

  (*   destruct (prefixes_from tp0' tp') as [| [??]] eqn:P'. *)
  (*   { inversion Heq. } *)
  (*   inversion Heq. subst. *)
    
  (*   destruct (decide (locale_of tp0 e = ζ)). *)
  (*   - symmetry. apply from_locale_from_lookup. erewrite <- IH; eauto. *)
  (*     2: {  *)
  (*     rewrite decide_True //; eauto. erewrite <-locale_equiv =>//. *)
  (*   - rewrite decide_False; last by erewrite <-locale_equiv. *)
  (*     apply Forall2_cons_1 in Heq as [Hlocs ?]. *)
  (*     rewrite decide_False // in Heζ; last by erewrite Hlocs, <-locale_equiv =>//. *)
  (*     apply (IH (tp0 ++ [e])); eauto. *)
  (*     apply locales_equiv_snoc =>//. *)
  (* Qed. *)

  Lemma call_continues_or_returns tpc c1 c2 τ
    (NVAL: nval_at tpc c1)
    (STEP: locale_step c1 (Some τ) c2):
    nval_at tpc c2 \/ exists r, return_at tpc c2 r.
  Proof using.
    red in NVAL. destruct NVAL as (e & EXPR & NVAL).
    pose proof EXPR as [eτi TI]%expr_at_in_locales%locales_of_cfg_Some.
    2: by apply c1. 
    red in EXPR. destruct tpc as [K' τ'].  
    (* pose proof EXPR as [eτi TI]%expr_at_in_locales%locales_of_cfg_Some. *)
    (* 2: { by apply c1. } *)
    inversion STEP. subst. inversion H3. subst. simpl in *.
    destruct (decide (τ' = locale_of t1 (fill K e1'))).
    2: { left. exists e. split; auto.
         red. rewrite -EXPR. simpl. 
         apply from_locale_from_app_Some in EXPR as [IN1 | IN2].
         { rewrite /from_locale. repeat erewrite from_locale_from_Some_app; eauto. }
         simpl in IN2. rewrite decide_False in IN2; [| done].
         rewrite /from_locale.
         symmetry. rewrite (app_assoc _ ([_])).
         erewrite from_locale_from_Some_app'; eauto.
         symmetry. apply from_locale_from_Some_app'. simpl.
         rewrite decide_False; [| done].
         apply from_locale_from_Some_app.
         apply from_locale_from_lookup in IN2 as (?&?). 
         eapply from_locale_from_lookup. split.
         - rewrite -H. rewrite !length_app /=. done.
         - etrans; [| apply H0]. rewrite !length_app /=. done. }

    subst τ'.
    rewrite /from_locale from_locale_from_locale_of in EXPR. inversion EXPR as [FILL'].
    rewrite FILL' in H3.
    apply fill_step_inv in H3; eauto. simpl in *.
    foobar. 

  Admitted.
    

  (* TODO: rename *)
  Lemma obls_terminates_impl_multiple_waitfree
    (extr : extrace heap_lang)
    (ETR0: exists e0, (trfirst extr).1 = [subst "m" m e0])
    (VALID: extrace_valid extr)
    (FAIR: fair_ex (tctx_tid ic) extr)
    (CALL: call_at extr m ic ai)
    (* (SPEC: wait_free_spec m) *)
    :
    terminating_trace extr \/ has_return extr ic. 
  Proof.
    opose proof * (simple_om_simulation_adequacy_terminate_multiple_waitfree) as ADEQ; eauto.

    destruct ADEQ as [| [n NFIT]]; [tauto| ].
    right. red. simpl in *.
    rewrite /fits_inf_call in NFIT.
    apply Classical_Prop.not_and_or in NFIT as [NFIT | X].
    2: apply Classical_Prop.not_and_or in X as [NFIT | NFIT].
    - destruct (trace_take_fwd n extr !! tctx_index ic) eqn:II; rewrite II /= // in NFIT.
      destruct NFIT.
      red in CALL. eauto. red.
      red in CALL. simpl in CALL.
      destruct ic. simpl in *. destruct CALL as (?&?&?).
      apply trace_take_fwd_lookup_Some in II.
      rewrite II in H. inversion H. subst x.
      eexists. do 2 (split; eauto).
      by rewrite under_ctx_fill.
    - apply not_forall_exists_not in NFIT. destruct NFIT as [r NFIT].
      apply Classical_Prop.imply_to_and in NFIT as [GE NFIT].
      destruct (trace_take_fwd n extr !! r) eqn:RR; rewrite RR /= // in NFIT.
      (* generalize call_continues_or_returns to sequence of transitions,
         use it from ic *)
      admit.
    - apply not_forall_exists_not in NFIT. destruct NFIT as [k NFIT].
      destruct (trace_take_fwd n extr !! k) eqn:KK; rewrite KK /= // in NFIT.
      destruct (from_locale c.1 (tctx_tid ic)) eqn:EE; rewrite EE /= // in NFIT.
      (* if k < n, it contradicts the call, as value won't reduce further *)
      (* otherwise, the context must be preserved, and it must be the return *)
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
