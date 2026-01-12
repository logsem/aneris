From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl gmultiset big_op mono_nat gmap_view.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len trace_utils. 
From trillium.program_logic Require Import execution_model weakestpre adequacy simulation_adequacy_em_cond. 
From trillium.prelude Require Import classical.
From fairness Require Import fairness locales_helpers utils.
From lawyer Require Import program_logic sub_action_em action_model.
From lawyer.examples Require Import orders_lib obls_tactics.
From lawyer.nonblocking Require Import trace_context om_wfree_inst pr_wfree_lib pr_wfree wfree_traces wptp_gen pwp calls.
From lawyer.nonblocking.logrel Require Import fundamental. 
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination.
From heap_lang Require Import lang simulation_adequacy.


Close Scope Z.


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
  Context (m ai: val).

  Context (s': stuckness).
  
  Definition obls_sim_rel_wfree extr omtr :=
    obls_sim_rel extr omtr /\ no_extra_obls ic (trace_last extr) (trace_last omtr) /\
    call_progresses ic s' extr. 

  Let fic := fits_inf_call ic m ai.

  Definition obls_st_rel_wfree c δ := 
    obls_st_rel c δ /\ no_extra_obls ic c δ. 

  Definition obls_om_traces_match_wfree: extrace heap_lang -> trace (mstate M) (mlabel M) -> Prop :=
    obls_om_traces_match_gen obls_st_rel_wfree. 

  Theorem om_simulation_adequacy_model_trace_multiple_waitfree Σ
        `{hPre: @heapGpreS Σ M EM} (s: stuckness)
        (es: list expr) σ1 (s1: mstate M) p
        (INIT: em_is_init_st (es, σ1) s1 (ExecutionModel := EM))
        (extr : extrace heap_lang)
        (Hvex : extrace_valid extr)
        (Hexfirst : trfirst extr = (es, σ1))
    :
    PR_premise_multiple obls_sim_rel_wfree (fits_inf_call ic m ai) Σ s es σ1 s1 (p: @em_init_param _ _ EM) ->
    (∃ omtr, obls_om_traces_match_wfree extr omtr ∧ trfirst omtr = s1 /\
              int_ref_inf obls_sim_rel_wfree extr omtr
    ) \/
    (exists k, ¬ (fits_inf_call ic m ai) (trace_take_fwd k extr)).
  Proof using.
    intros PREM.

    destruct (decide (1 <= length es)).
    2: { 
      (* TODO: make a lemma *)
         assert (length es = 0) by lia.
         assert (es = []) as -> by (destruct es; simpl in H; lia || done).
         assert (extr = tr_singl ([], σ1)) as ->.
         { destruct extr; simpl in Hexfirst; subst. 
           { done. }
           apply extrace_valid_alt, trace_valid_cons_inv, proj2 in Hvex.
           inversion Hvex; subst; try done.
           inversion H0. clear -H4.
           apply (@f_equal _ _ length) in H4.
           rewrite !length_app /= in H4. lia. }

         destruct (decide (fits_inf_call ic m ai ({tr[ ([], σ1) ]}))) as [FITS | ].
         2: { right. exists 0. by rewrite trace_take_fwd_0_first. }
         
         assert (obls_st_rel_wfree ([], σ1) s1) as PROP. 
         { red. 
           rewrite /obls_st_rel /no_extra_obls.
           rewrite /obls_fairness_preservation.om_live_tids /has_obls.
           simpl in INIT. red in INIT.
           rewrite /locales_of_cfg in INIT. rewrite list_to_set_nil in INIT.
           apply proj1, eq_sym, dom_empty_inv_L in INIT.
           rewrite INIT.
           split; try set_solver. }

         left. exists (tr_singl s1).

         split.
         2: { split; [done| ].
              apply int_ref_int_singleton.
              red.
              repeat split; try by apply PROP.
              red. simpl. intros _ TI0.
              assert (tctx_index ic = 0) by lia.
              destruct FITS as [CALL _ _ _].
              rewrite H0 /= in CALL.
              rewrite /call_at /= in CALL.
              by edestruct no_expr_in_empty_pool. }

         red. by apply trace_match_singl. }

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

  Open Scope WFR_scope. 

  Context (P: val -> Prop) (Pai: P ai).
  Context (SPEC: WaitFreeSpec s' P m).
  Let F := wfs_F _ _ _ SPEC.

  Definition init_om_wfree_state
    (* (F: nat) (TI: nat) (d0 d1: Degree) (τi: locale Λ) (l0: Level) (ii: nat) *)
    (c: cfg heap_lang): ProgressState :=
    let CPS := (2 * (F ai) + ii) *: {[+ d0 +]} ⊎ {[+ d1 +]} in
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
    (cp_mul π0 d0 (2 * (F ai)) ∗ cp_mul π0 d0 ii ∗ cp π0 d1) ∗
    (⌜ τi ∈ locales_of_cfg c ⌝ →
     ∃ s, obls τi {[ s ]} ∗ sgn s l0 (Some false) ∗ ep s π0 d0) ∗
    ([∗ set] τ ∈ locales_of_cfg c ∖ {[ τi ]}, obls τ ∅) ∗
    ([∗ set] τ ∈ locales_of_cfg c, ∃ π, th_phase_eq τ π).  
  Proof using.
    clear dependent Pai. 
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

  Lemma init_pwp {Σ} {hG :heap1GS Σ} {iG: invGS_gen HasNoLc Σ} τ e0
    (VALID: valid_client e0):
    let _ := irisG_looping HeapLangEM si_add_none (lG := hG) in 
    wfs_mod_inv _ _ _ SPEC ⊢ pwp MaybeStuck ⊤ τ (subst "m" m e0) (λ _, True).
  Proof using SPEC.
    simpl. opose proof * (fundamental e0) as FTLR. 
    { done. }
    iIntros "#INV". 
    rewrite /logrel in FTLR.
    rewrite /interp_expr in FTLR.
    rewrite -subst_env_singleton.
    iApply wp_wand; [iApply FTLR| ].
    - rewrite -insert_empty. iApply interp_env_cons; [done| ].
      iSplitL; [| by iApply interp_env_nil].
      destruct SPEC. by iApply wfs_safety_spec. 
    - by iIntros "**".
  Qed. 

  Lemma init_wptp_wfree_pwps `{Hinv: @IEMGS _ _ HeapLangEM EM Σ} tp0 tp N
    (NO: τi ∉ locales_of_list_from tp0 tp)
    (SUBST: Forall (λ e, ∃ e0, e = subst "m" m e0 /\ valid_client e0) tp):
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfs_mod_inv _ _ _ SPEC)
   ⊢ wptp_from_gen (thread_pr ic s' MaybeStuck N) tp0 tp
      (map (λ (_ : nat) (_ : val), ⌜ True ⌝%I)
         (adequacy_utils.locales_of_list_from tp0 tp)).
  Proof using SPEC ai.
    clear Pai. 
    iIntros "#INV". 
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
    inversion SUBST as [| ?? (? & -> & ?)]. subst. 
    by iApply init_pwp.
  Qed.

  Definition tpool_init_restr (tp: list expr) :=
    Forall (fun e => exists e0, e = subst "m" m e0 /\ valid_client e0) tp /\
    (ii = 0 -> exists e, from_locale tp τi = Some e /\ under_ctx Ki e = Some (m ai)) /\
    (forall e, from_locale tp τi = Some e -> to_val e = None). 

  Lemma init_wptp_wfree `{Hinv: @IEMGS _ _ HeapLangEM EM Σ} c
    (ETR0: tpool_init_restr c.1):
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfs_mod_inv _ _ _ SPEC) -∗
    (⌜ ii = 0 ⌝ → ∃ π, cp_mul π0 d0 (F ai) ∗ th_phase_frag τi π (/2)%Qp) -∗
    wptp_wfree ic s' MaybeStuck {tr[ c ]}
      (map (λ _ _, True) (adequacy_utils.locales_of_list c.1)).
  Proof using Pai.
    simpl. iIntros "#INV T".
    rewrite /wptp_wfree. simpl. 
    destruct (thread_pool_split c.1 τi) as (tp1 & tp2 & tp' & EQ & TP' & NO1 & NO2).
    rewrite EQ. rewrite !locales_of_list_from_app'. rewrite !map_app /=.
    destruct ETR0 as (TP & II0 & NVAL0).
    rewrite EQ in TP.
    iApply wptp_from_gen_app. iSplitR.
    { iApply init_wptp_wfree_pwps.
      - done. 
      - by apply Forall_app, proj1 in TP.
      - done. }
    simpl. iApply wptp_from_gen_app. iSplitL.
    2: { iApply init_wptp_wfree_pwps.
         - done. 
         - by do 2 (apply Forall_app, proj2 in TP).
         - done. }

    destruct TP' as [-> | (e & -> & LOC)].
    { simpl. iApply wptp_from_gen_nil. }
    simpl. iApply wptp_gen_singleton.
    rewrite /thread_pr. rewrite decide_True; [| done].
    rewrite /wp_tc.
    destruct ii eqn:TI.
    2: { rewrite leb_correct; [| lia].
         apply Forall_app, proj2 in TP.
         apply Forall_app, proj1 in TP.
         inversion TP as [| ?? (? & -> & ?)]. subst.
         by iApply init_pwp. }
    rewrite leb_correct_conv; [| lia].
    iDestruct ("T" with "[//]") as (π) "[CPS PH]".
    rewrite half_inv2. 
    iPoseProof (get_call_wp _ _ SPEC ai with "[$] [$] [$]") as "WP".
    { done. }
    destruct (II0 eq_refl) as (e_ & IN & CTX).
    rewrite LOC EQ /= in IN.
    rewrite /from_locale in IN. rewrite from_locale_from_locale_of in IN.
    inversion IN. subst e_.
    rewrite CTX. simpl.
    iApply (wp_stuck_mono with "[$]"). done.
  Qed.

  Lemma tp_init_in tp τ
    (IN: τ ∈ locales_of_list tp)
    (ETR0: tpool_init_restr tp):
    exists e0, from_locale tp τ = Some (subst "m" m e0).
  Proof using.
    clear -IN ETR0. 
    destruct ETR0 as [TP _].
    apply elem_of_locales_of_list_from_from_locale_from in IN as (e & IN).
    rewrite /from_locale IN.
    apply Forall_forall with (x := e) in TP; [set_solver| ].
    eapply from_locale_from_elem_of; eauto.
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

  Lemma PR_premise_wfree `{hPre: @heapGpreS Σ M EM} c
    (ETR0: tpool_init_restr c.1)
    (MOD_INIT: wfs_is_init_st _ _ m SPEC c)
    (M_FUN: exists f x b, m = RecV f x b)
    :
  PR_premise_multiple obls_sim_rel_wfree (fits_inf_call ic m ai)
    Σ MaybeStuck c.1 c.2
    (init_om_wfree_state c) ((): @em_init_param _ _ EM).
  Proof using Pai.
    red. iIntros (Hinv) "(PHYS & MOD)". simpl.
    iMod (@wfs_init_mod _ _ _ SPEC with "[PHYS]") as "#INV".
    2: { iFrame. }
    { by rewrite -surjective_pairing. } 
         
    iModIntro.
    iExists (wfree_trace_inv ic s' SPEC).
    
    iExists (PR_wfree ic s' SPEC _ Pai). simpl.

    do 2 rewrite bi.sep_assoc. iSplitL.
    2: { rewrite /adequacy_cond.rel_always_holds_with_trace_inv.

         iIntros (extr omtr [tp σ] EXTRA FIN NSTUCK).
         iClear "INV".
         simpl. iIntros "(%VALID_STEP & HEAP & MSI & [%TH_OWN %OBLS]) POSTS #INV".
         red in EXTRA. destruct EXTRA as (VALID & EX0 & OM0 & CONT_SIM). 
         iApply fupd_mask_intro_discard; [done| ].

         rewrite /wfree_trace_inv. iDestruct "INV" as "((%NOOBS' & %NVAL & %PROGRESS) & _)".
         iPureIntro. 

         rewrite /obls_sim_rel_wfree. split; [|done].

         destruct extr.
         { simpl in VALID_STEP.
           inversion VALID. subst.
           red in EX0, OM0. simpl in EX0, OM0. subst.
           rewrite /obls_sim_rel_wfree /obls_sim_rel /obls_sim_rel_gen.
           simpl.

           split; [done| ]. simpl. red.
           red. simpl. eapply @obls_τi_enabled; eauto. }
         
         simpl in VALID_STEP. inversion VALID. subst. simpl in *.
         rewrite /obls_sim_rel.
         red. split. 
         { simpl. by destruct a. }
         simpl. rewrite /obls_st_rel.
         red. simpl.
         eapply @obls_τi_enabled; eauto. }

    rewrite -surjective_pairing. 
    iSplitL.
    2: { rewrite /wfree_trace_inv. iFrame "INV". 
         iPureIntro. repeat split.
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
           by apply NVAL0 in IN.
         - red. simpl.
           intros _ TI0.
           destruct ETR0 as (?&CALL0&?).
           destruct (CALL0 ltac:(lia)) as (?&?&?).           
           eapply RecV_App_not_stuck; eauto. }
    
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
    { iSplitL.
      2: by destruct s'. 
      destruct decide.
      - iSpecialize ("OB'" with "[//]"). iFrame.
      - iFrame. }

    iApply (init_wptp_wfree with "[$] [$]"). done. 
  Qed.

  Definition wfreeΣ: gFunctors := iemΣ HeapLangEM EM. 

  Instance wfree_pre: @heapGpreS wfreeΣ M EM.
  Proof. 
    unshelve esplit. 
  Qed. 

  Local Lemma tc_helper:
    tctx_tpctx ic = {| tpctx_ctx := Ki; tpctx_tid := τi |}.
  Proof using. clear. by destruct ic as [? []]. Qed.

  Local Lemma ic_helper:
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
  (* (PROGRESS: *)
  (*   forall j, ii <= j ->  *)
  (*   from_option (not_stuck_tid τi) True (extr S!! j) *)
  (* ) *)
  (PROGRESS: exists N, ii <= N /\ is_Some (extr S!! N) /\ ∀ j, N ≤ j → from_option (not_stuck_tid τi) True (extr S!! j))
    :
  ∀ τ, obls_trace_fair τ omtr.
  Proof using.
    clear m SPEC F fic.
    clear dependent ai.
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
  Instance under_ctx_ex_dec (extr: extrace heap_lang):
    Decision (∃ e, from_locale (trfirst extr).1 τi = Some e ∧ under_ctx Ki e = Some (m ai)).
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

  (* TODO: find existinc *)
  Instance stuckness_eqdec: EqDecision stuckness.
  Proof using. red. intros [] []; (by left) || (by right). Qed. 

  (* TODO: use this def above *)
  Definition never_stuck_ea (etr: extrace heap_lang) '(TraceCtx i (TpoolCtx K τ)) :=
    ∃ N, i ≤ N ∧ is_Some (etr S!! N)
      ∧ ∀ j, N ≤ j → from_option (not_stuck_tid τ) True (etr S!! j).

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

  (* Lemma not_gets_stuck_ae_equiv etr tc: *)
  (*   (¬ gets_stuck_ae etr tc) <-> never_stuck_ea etr tc. *)
  (* Proof using. *)
  (*   destruct tc as [? [??]].  *)
  (*   rewrite /gets_stuck_ae /never_stuck_ea. *)
  (*   split. *)
  (*   -  *)
  (*     rewrite not_all_ex_not_iff. intros (N & NS).   *)
  (*     rewrite not_impl_and_not_iff.  *)
  (*     do 2 rewrite (and_comm (is_Some (etr S!! x)) _). *)
  (*     rewrite and_assoc.  *)
  (*     do 2 rewrite (and_comm _ (is_Some (etr S!! x))). *)

  (*     apply traces.utils_logic.iff_and_pre. intros. *)
  (*   rewrite not_ex_all_not_iff. *)
  (*   split. *)
  (*   - intros. *)
  (*     destruct (decide (tctx_index <= x)). *)
  (*     2: { specialize (H0 x). *)
  (*          eapply @not_and_l in H0. *)
  (*          2: { rewrite /ge; solve_decision. } *)
  (*          destruct H0 as [? | X]; [lia| ]. *)
  (*          apply not_and_l in X. *)
  (*          destruct X as [? | X]; [done| ]. *)
           
           

  (* TODO: rename *)
  Lemma simple_om_simulation_adequacy_terminate_multiple_waitfree_impl extr
    (MOD_INIT : wfs_is_init_st s' _ m SPEC (trfirst extr))
    (VALID : extrace_valid extr)
    (FAIR : fair_call extr tpc ii)
    (INIT_TP : tpool_init_restr (trfirst extr).1)
    (CALL: from_option (fun c => call_at tpc c m ai (APP := App)) False (extr S!! ii))
    (M_FUN: exists f x b, m = RecV f x b):
    terminating_trace extr /\ int_ref_inf_one (call_progresses ic s') extr ∨
    (∃ k, ¬ fits_inf_call ic m ai (trace_take_fwd k extr)) \/
    (s' = MaybeStuck /\ gets_stuck_ae extr ic). 
  Proof using Pai.
    opose proof (om_simulation_adequacy_model_trace_multiple_waitfree
                wfreeΣ _ (trfirst extr).1 _ _ _ _ _ VALID _ _) as ADEQ.
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
    { red in RET. rewrite ic_helper in RET.
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
         clear -IREF H ITH S'.
         red in IREF.
         specialize (IREF j). red in IREF. do 2 apply proj2 in IREF.
         red in IREF.
         
         (* TODO: make a lemma *)
         pose proof (trace_has_len extr) as [? LEN].
         pose proof ITH as LT%mk_is_Some. eapply state_lookup_dom in LT; eauto.
         assert (trace_length (trace_take_fwd j extr) = S j).
         { apply Nat.le_antisymm.
           1: by apply trace_take_fwd_length_bound.
           opose proof * (trace_take_fwd_length j extr); eauto.
           destruct x; try lia.
           rewrite H0.
           simpl in LT. lia. }
         rewrite H0 in IREF. ospecialize * IREF; try (done || lia).
         { clear -S'. by destruct s'. }
         symmetry in H0. apply trace_lookup_last in H0.
         eapply trace_take_fwd_lookup_Some' in ITH; [| reflexivity].
         set_solver. }
    
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
    rewrite ic_helper /tpc tc_helper in NS.
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
        (ETR0: valid_init_tpool m (trfirst extr).1)
        (MOD_INIT: wfs_is_init_st _ _ _ SPEC (trfirst extr))
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

    assert (tpool_init_restr (trfirst extr).1) as INIT_TP.
    { repeat split; eauto. }

    by apply simple_om_simulation_adequacy_terminate_multiple_waitfree_impl.
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
    clear dependent ic. clear dependent m. 
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

  (* TODO: rename *)
  Lemma obls_terminates_impl_multiple_waitfree
    (extr : extrace heap_lang)
    (ETR0: valid_init_tpool m (trfirst extr).1)
    (MOD_INIT: wfs_is_init_st _ _ _ SPEC (trfirst extr))
    (VALID: extrace_valid extr)
    (* (FAIR: fair_ex τi extr) *)
    (FAIR: fair_call extr tpc ii)
    (MAIN: previous_calls_return_tr extr ii τi m)
    (CALL: from_option (fun c => call_at tpc c m ai (APP := App)) False (extr S!! ii))
    (M_FUN: exists f x b, m = RecV f x b)
    :
    terminating_trace extr /\ int_ref_inf_one (call_progresses ic s') extr
    \/ has_return extr ic \/
    (s' = MaybeStuck /\ gets_stuck_ae extr ic). 
  Proof.
    opose proof * (simple_om_simulation_adequacy_terminate_multiple_waitfree) as ADEQ; eauto.

    destruct ADEQ as [| [[n NFIT] | STUCK]]; [tauto| | tauto]. 
    right. left. red. simpl in *.
    (* rewrite /fits_inf_call in NFIT. *)
    destruct (extr S!! ii) as [ci | ] eqn:ITH; rewrite ITH /= in CALL; [| done].
    pose proof (FIC ic m ai (trace_take_fwd n extr)) as X.
    rewrite !curry_uncurry_prop in X. apply Classical_Prop.imply_to_or in X.
    destruct X as [NFIT' | ?]; [| done]. clear NFIT. rename NFIT' into NFIT.
    apply Classical_Prop.not_and_or in NFIT as [X | NFIT].
    1: apply Classical_Prop.not_and_or in X as [X | NFIT].
    1: apply Classical_Prop.not_and_or in X as [NFIT | NFIT].
    - destruct (trace_take_fwd n extr !! tctx_index ic) eqn:II; rewrite II /= // in NFIT.
      destruct NFIT.
      apply trace_take_fwd_lookup_Some in II.
      fold ii in II. rewrite II in ITH. inversion ITH. 
      eauto. 
    - apply not_forall_exists_not in NFIT. destruct NFIT as [r NFIT].
      apply Classical_Prop.imply_to_and in NFIT as [GE NFIT].
      destruct (trace_take_fwd n extr !! r) eqn:RR; rewrite RR /= // in NFIT.
      
      eapply call_returns_if_not_continues in NFIT; eauto.
      3: by apply trace_take_fwd_lookup_Some in RR.
      2: { eapply call_nval_at; eauto. done. }
      rename r into b. 
      destruct NFIT as (k & r & ck & RANGE & KTH & RETk).
      rewrite ic_helper.
      exists k, r, ck. split; eauto. lia.
    - apply not_forall_exists_not in NFIT. destruct NFIT as [j NFIT].
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
    - apply Classical_Prop.imply_to_and in NFIT as [LONG NORET].
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
     
End WFAdequacy.


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


Definition always_returns_main s P m tr :=
  forall tc a ci, let '(TraceCtx i tpc) := tc in
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
Lemma main_returns_reduction s' m etr
  (VALID: extrace_valid etr)
  (M_FUN: exists f x b, m = RecV f x b):
  always_returns_main s' any_arg m etr -> always_returns m s' any_arg etr.
Proof using.
  rewrite /always_returns_main /always_returns. 
  intros MAIN_RET. intros [i [K τ]] a ci FAIR ITH CALL _.

  odestruct (@Classical_Prop.classic _) as [RET | NORET]; [by apply RET| ].
  apply Classical_Prop.not_or_and in NORET as (NORET & ?). 
  
  opose proof * find_main_call as X; eauto.

  destruct X as (j & K' & a' & c' & ?&?&?&?&PREV&NVALj).
  ospecialize * (MAIN_RET (TraceCtx j (TpoolCtx K' τ))).
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


Theorem wfree_is_wait_free s' m
  (SPEC: WaitFreeSpec s' any_arg m)
  (M_FUN: exists f x b, m = RecV f x b):
  wait_free m (wfs_is_init_st _ _ _ SPEC) s' any_arg.
Proof using.
  red. intros etr ETR0 MOD_INIT VALID.
  apply main_returns_reduction; try done. 
  red. intros [i tpc] a ci FAIR ITH MAIN CALL _.

  opose proof * (obls_terminates_impl_multiple_waitfree (TraceCtx i tpc)) as ADEQ.
  3: by apply MOD_INIT. 
  all: eauto.
  { done. }
  { simpl. by rewrite ITH. }
  
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
    
    pose proof DOM as EE. eapply from_locale_trace in EE; eauto.
    2: { eapply locales_of_cfg_Some. eapply expr_at_in_locales.
         erewrite <- surjective_pairing. eauto. }
    rewrite LAST /= in EE. destruct EE as [e EE].
    
    destruct (decide (nval_at tpc c)) as [NVAL | VAL]. 
    + clear ITH.
      clear CALL.
      clear MOD_INIT.
      clear VALID.
      clear ETR0 SPEC.
      
      (* clear DOM.  *)
      
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
    + eapply call_returns_if_not_continues in DOM; eauto.
      2: { eapply call_nval_at; eauto. done. }
      destruct DOM as (k & r & ck & RANGE & KTH & RETk).
      red. exists k, r, ck. split; eauto. lia. }
  
  destruct s'.
  2: {
       destruct (decide (not_stuck_tid (tpctx_tid tpc) c)).
       - by apply IF_NS.
       - right. split; auto.
         red. intros N [? NTH].
         exists (len - 1). repeat split; eauto.
         { red. eapply mk_is_Some, state_lookup_dom in NTH; eauto.
           simpl in NTH. lia. }
         red. destruct tpc.
         eexists. repeat split; eauto.
         apply stuck_tid_neg. split; auto.
         eapply from_locale_trace in DOM; eauto.
         by rewrite LAST in DOM. }
  
  apply IF_NS. 
  
  opose proof * (trace_take_fwd_length len etr) as LEN'; eauto. simpl in LEN'.
  (* TODO: make a lemma, remove duplicate above *)
  red in PROGRESS. ospecialize (PROGRESS len _ _); [done| ..]. 
  { simpl. simpl in *.
    rewrite LEN'. rewrite Nat.min_l; [| lia].
    apply trace_len_gt_0 in LEN. simpl in LEN.
    lia. }      
  simpl in *.
  eapply trace_take_fwd_lookup_Some' in LAST.
  2: { apply Nat.le_succ_diag_r. }
  pose proof LEN as ?%trace_len_gt_0. simpl in H. 
  replace (S (len - 1)) with len in LAST; [| lia]. 
  
  erewrite trace_lookup_last in LAST.
  2: { rewrite LEN'. lia. }
  by inversion LAST.
Qed.

Print Assumptions wfree_is_wait_free.
