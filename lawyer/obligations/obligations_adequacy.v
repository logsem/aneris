From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From trillium.traces Require Import trace_lookup.
From fairness Require Import locales_helpers comp_utils fairness fin_branch utils_tactics.
From heap_lang Require Import simulation_adequacy locales_helpers_hl.
From lawyer Require Import sub_action_em action_model.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_em obls_fairness_preservation obligations_am obligations_fin_branch obls_termination obligations_wf obligations_logic env_helpers.


Section OblsAdequacy.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}.
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.

  Let M := AM2M ObligationsAM.
  
  Definition obls_st_rel (c: cfg heap_lang) (δ: mstate M) :=
    om_live_tids id locale_enabled c δ.
    
  Definition obls_sim_rel_gen
    (SR: cfg heap_lang -> mstate M -> Prop)
    (extr: execution_trace heap_lang) (omtr: auxiliary_trace M) :=
    valid_state_evolution_fairness
      (obls_ves_wrapper: cfg heap_lang -> olocale heap_lang -> cfg heap_lang -> mstate M -> mlabel M -> mstate M -> Prop)
      extr omtr ∧
      SR (trace_last extr) (trace_last omtr).

  Definition obls_sim_rel := obls_sim_rel_gen obls_st_rel. 

  Definition obls_om_traces_match_gen (SR: cfg heap_lang -> mstate M -> Prop):
    extrace heap_lang -> trace (mstate M) (mlabel M) -> Prop :=
    traces_match
      (fun oτ '(_, τ') => oτ = τ')
      SR
      locale_step
      (@mtrans M).

  Definition obls_om_traces_match := obls_om_traces_match_gen obls_st_rel.

  Hypotheses (FIN_LVL: finite.Finite LevelO) (FIN_DEG: finite.Finite DegO).

  Lemma obls_sim_rel_FB: rel_finitary obls_sim_rel.
  Proof using FIN_LVL FIN_DEG.
    clear -FIN_LVL FIN_DEG. red. intros extr mtr [tp' σ'] oζ.
    simpl. rewrite /obls_sim_rel. simpl.
    rewrite /obls_valid_evolution_step /obls_st_rel. simpl.
    apply list_approx_smaller_card.
    apply @OM_fin_branch_impl; eauto.
    apply _.
  Qed.
    
  Theorem om_simulation_adequacy_model_trace_multiple Σ
        `{hPre: @heapGpreS Σ M EM}
        SR
        (s: stuckness)
        (es: list expr) σ1 (s1: mstate M) p
        (INIT: em_is_init_st (es, σ1) s1 (ExecutionModel := EM))
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : trfirst extr = (es, σ1))
        (LEN: length es ≥ 1)
        (FB: rel_finitary (obls_sim_rel_gen SR)):
    wp_premise_multiple (obls_sim_rel_gen SR) Σ s es σ1 s1 (p: @em_init_param _ _ EM) ->
    ∃ (omtr: trace (mstate M) (mlabel M)),
      obls_om_traces_match_gen SR extr omtr ∧
      trfirst omtr = s1.
  Proof using FIN_LVL FIN_DEG.
    intros PREM.

    unshelve epose proof (@strong_simulation_adequacy_traces_multiple_HL _ _ _ hPre s es σ1
                s1
                (obls_sim_rel_gen SR)
                p
                extr
                Hvex
                ltac:(done)
                obls_ves_wrapper
                SR
                (fun oτ '(_, τ') => oτ = τ')
                _ _ _ _ _ _ _
      ) as SIM.
    { simpl. intros ????[??]? STEP.
      red in STEP. simpl in STEP. destruct STEP as [STEP ->].
      destruct o; [| done].
      simpl in STEP. red in STEP. apply STEP. }
    { simpl. intros ????[??]? STEP.
      red in STEP. simpl in STEP. destruct STEP as [STEP ->].
      destruct o; [| done].
      simpl in STEP. red in STEP.
      constructor. apply STEP. }
    { simpl. intros ?? SIM. apply SIM. }
    { simpl. intros ?? SIM. apply SIM. }
    { done. }
    { done. }
    { done. }
    eapply SIM; eauto. 
  Qed.

  Theorem om_simulation_adequacy_model_trace Σ
        `{hPre: @heapGpreS Σ M EM}
        SR
        (s: stuckness)
        (e1: expr) σ1 (s1: mstate M) p
        (INIT: em_is_init_st ([e1], σ1) s1 (ExecutionModel := EM))
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : trfirst extr = ([e1], σ1))
        (FB: rel_finitary (obls_sim_rel_gen SR)):
    wp_premise (obls_sim_rel_gen SR) Σ s e1 σ1 s1 (p: @em_init_param _ _ EM) ->
    ∃ (omtr: trace (mstate M) (mlabel M)),
      (obls_om_traces_match_gen SR) extr omtr ∧
      trfirst omtr = s1.
  Proof using FIN_LVL FIN_DEG.
    intros. eapply om_simulation_adequacy_model_trace_multiple; last first.
    { by eapply wp_premise_single. }
    all: eauto. 
  Qed.

  Hypotheses (WF_LVL: well_founded (strict lvl_le)) (WF_DEG: well_founded (strict deg_le)).

  Definition exec_OM_traces_match :=
    out_om_traces_match locale_step Some
      (fun oτ c => from_option (fun τ => locale_enabled τ c) False oτ).

  Definition om_tr_wf (omtr: obls_trace) :=
    ∀ i δ, omtr S!! i = Some δ → om_st_wf δ. 

  Lemma om_st_wf_tr omtr
    (VALID: trace_valid om_trans omtr)
    (WF0: om_st_wf (trfirst omtr)):
    om_tr_wf omtr.
  Proof using. 
    intros i δ ITH. eapply pres_by_valid_trace with (i := 0) (j := i) in VALID.
    2: apply wf_preserved_by_loc_step.
    2: apply wf_preserved_by_fork_step.
    2: { by rewrite state_lookup_0. }
    2: lia.
    by rewrite ITH in VALID. 
  Qed.

  (* TODO: move to Trillium*)
Lemma traces_match_impl_strong {S1 S2 L1 L2}
      (Rℓ1: L1 -> L2 -> Prop) (Rs1: S1 -> S2 -> Prop)
      (Rℓ2: L1 -> L2 -> Prop) (Rs2: S1 -> S2 -> Prop)
      (trans1 trans1': S1 -> L1 -> S1 -> Prop)
      (trans2 trans2': S2 -> L2 -> S2 -> Prop)
      tr1 tr2 :
  (∀ ℓ1 ℓ2, Rℓ1 ℓ1 ℓ2 → Rℓ2 ℓ1 ℓ2) →
  (∀ s1 s2, Rs1 s1 s2 → Rs2 s1 s2) →
  (forall s ℓ s', trans1 s ℓ s' -> trans1' s ℓ s') ->
  (forall s ℓ s', trans2 s ℓ s' -> trans2' s ℓ s') ->
  traces_match Rℓ1 Rs1 trans1 trans2 tr1 tr2 →
  traces_match Rℓ2 Rs2 trans1' trans2' tr1 tr2.
Proof.
  intros HRℓ HRs T1 T2. revert tr1 tr2. cofix IH. intros tr1 tr2 Hmatch.
  inversion Hmatch; simplify_eq.
  - constructor 1. by apply HRs.
  - constructor 2; [by apply HRℓ|by apply HRs|..].
    3: by apply IH.
    all: eauto. 
Qed.

  Lemma obls_matching_traces_OM SR extr mtr
    (SR_LIVE: forall c δ, SR c δ -> obls_st_rel c δ)
    (MATCH: obls_om_traces_match_gen SR extr mtr)
    (WF0: om_st_wf (trfirst mtr))
    :
    ∃ (omtr: obls_trace),
      exec_OM_traces_match extr omtr ∧
      traces_match (fun _ _ => True) SR (fun _ _ _ => True) (fun _ _ _ => True) extr omtr /\
      om_tr_wf omtr /\
      trfirst omtr = trfirst mtr.
  Proof using.
    clear -MATCH OM WF0 SR_LIVE.
    assert (exists omtr, traces_match (fun ℓ τ => ℓ.2 = Some τ) eq (@mtrans M) (@mtrans OM) mtr omtr) as [omtr MATCHo].
    { clear -MATCH mtr.
      exists (project_nested_trace id ((mbind Some) ∘ snd) mtr).
      eapply trace_utils.traces_match_impl.
      3: { eapply nested_trace_construction.
           - eapply traces_match_valid2; eauto.
           - simpl. intros. simpl.
             rewrite /step_label_matches. destruct res.
             destruct o as [[[??]?]|].
             2: { right. red. eauto. }
             left. do 3 eexists. split; [reflexivity| ]. simpl.
             destruct o; [done| ].
             apply traces_match_valid2 in MATCH.
             eapply trace_valid_steps' in H; eauto. inversion H.
           - intros. destruct ℓ. simpl in H0. destruct o; [| done].
             simpl in H0. inversion H0. subst. simpl.
             inversion H. subst. eauto. }
      2: done.
      simpl. intros [??] ?. simpl. destruct o; done. }
   
    pose proof (traces_match_compose _ _ _ MATCH MATCHo) as MATCH'.

    assert (out_om_traces_match locale_step Some
              (fun oτ c => from_option (fun τ => locale_enabled τ c) False oτ)
              extr omtr) as MATCH''.
    { eapply trace_utils.traces_match_impl; [..| apply MATCH'].
      - simpl. intros ?? ([??] & <- & ?). done.
      - simpl. intros ?? (? & ? & ?). subst. 
        eapply SR_LIVE; eauto. }

    eexists. split; eauto. split_and !.
    - eapply traces_match_impl_strong. 
      5: by apply MATCH'.
      all: eauto.
      simpl. set_solver. 
    - eapply om_st_wf_tr.
      + eapply traces_match_valid2; eauto.
      + apply traces_match_first in MATCHo.
        by rewrite MATCHo in WF0.
    - by apply traces_match_first in MATCHo.
  Qed.

  Lemma exec_om_fairness_preserved extr omtr τ:
      exec_OM_traces_match extr omtr ->
      fair_ex τ extr → obls_trace_fair τ omtr.
  Proof using.
    intros MATCH FAIR.
    eapply out_om_fairness_preserved_single.
    2: apply MATCH.
    { apply _. }

    red. simpl. clear -FAIR.
    apply fair_by_equiv. red. intros n EN. simpl in EN.
    destruct (extr S!! n) eqn:NTH; rewrite NTH in EN; [| done].
    simpl in EN. simpl.
    apply fair_by_equiv in FAIR.
    
    ospecialize (FAIR n ltac:(by rewrite NTH)).
    destruct FAIR as (?&?&?&FAIR).
    do 2 eexists. split; eauto.
    destruct FAIR as [| FAIR].
    { left. done. }
    right. destruct FAIR as (?&?&?). eauto.
  Qed.

  Lemma obls_matching_traces_termination extr mtr
    (OM_WF0: om_st_wf (trfirst mtr))
    (FAIR: ∀ tid, fair_ex tid extr)
    (MATCH: obls_om_traces_match extr mtr)
    :
    terminating_trace extr.
  Proof using WF_LVL WF_DEG.
    clear -MATCH FAIR OM OM_WF0 WF_LVL WF_DEG.

    opose proof (obls_matching_traces_OM _ _ _ _ MATCH OM_WF0) as (omtr & MATCH'' & OM_WF & FIRST'' & ?).
    { done. }

    assert (forall τ, obls_trace_fair τ omtr) as OM_FAIR.
    { intros. eapply exec_om_fairness_preserved; eauto. } 

    pose proof (traces_match_valid2 _ _ _ _ _ _ MATCH'') as OM_VALID.
    pose proof (obls_fair_trace_terminate _ OM_VALID OM_FAIR) as OM_TERM.

    eapply (traces_match_preserves_termination _ _ _ _ _ _ MATCH'').
    apply OM_TERM; eauto. 
  Qed.

  Let ASEM := ObligationsASEM.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} τ _ => obls τ ∅ (oGS := aGS)).

  Lemma obls_init_wf es σ1 s1
    (INIT: obls_is_init_st (es, σ1) s1):
    om_st_wf s1.
  Proof using.
    clear -INIT. 
    red in INIT. set_solver.
  Qed. 

  Theorem simple_om_simulation_adequacy_terminate_multiple Σ
        `{hPre: @heapGpreS Σ M EM} (s: stuckness)
        es σ1 (s1: mstate M) p
        (INIT: em_is_init_st (es, σ1) s1 (ExecutionModel := EM))
        (extr : heap_lang_extrace)
        (Hexfirst : trfirst extr = (es, σ1))
        (LEN: length es ≥ 1):
    wp_premise_multiple obls_sim_rel Σ s es σ1 s1 (p: @em_init_param _ _ EM) ->
    extrace_fairly_terminating extr.
  Proof.
    rewrite /extrace_fairly_terminating.
    intros Hwp VALID FAIR.

    odestruct (om_simulation_adequacy_model_trace_multiple
                Σ _ _ es _ s1 _ INIT _ VALID Hexfirst LEN _ Hwp) as (omtr&MATCH&OM0).
    { apply obls_sim_rel_FB. }

    eapply obls_matching_traces_termination; eauto.
    rewrite OM0. simpl in INIT.
    eapply obls_init_wf; eauto. 
  Qed.

  Theorem simple_om_simulation_adequacy_terminate Σ
        `{hPre: @heapGpreS Σ M EM} (s: stuckness)
        (e1: expr) σ1 (s1: mstate M) p
        (INIT: em_is_init_st ([e1], σ1) s1 (ExecutionModel := EM))
        (extr : heap_lang_extrace)
        (Hexfirst : trfirst extr = ([e1], σ1)):
    wp_premise obls_sim_rel Σ s e1 σ1 s1 (p: @em_init_param _ _ EM) ->
    extrace_fairly_terminating extr.
  Proof.
    intros. eapply simple_om_simulation_adequacy_terminate_multiple; last first.
    { by eapply wp_premise_single. }
    all: by eauto. 
  Qed.

  Lemma om_live_tids_init es σ ds eb:
    om_live_tids id locale_enabled (es, σ) (init_om_state (es, σ) ds eb).
  Proof using.
    clear. 
    red. intros ?.
    rewrite /has_obls. simpl.
    rewrite locales_of_cfg_simpl. simpl.

    destruct lookup eqn:IN; simpl; try done.
    apply lookup_gset_to_gmap_Some in IN. set_solver. 
  Qed.

  Lemma no_obls_live_tids_multiple {Σ: gFunctors} {Hinv: @heapGS Σ M EM}
    (oGS := @heap_fairnessGS Σ _ _ Hinv)
    (tp : list expr) (σ : state) (δ' : ProgressState)
    (TH_OWN : threads_own_obls (tp, σ) δ'):
    gen_heap_interp (heap σ) -∗ obls_msi δ' (oGS := oGS) -∗
      (let Φs := map (fun τ v => @em_thread_post heap_lang M EM Σ (@heap_fairnessGS Σ M EM _) τ v) (seq 0 (length tp)) in
      posts_of tp Φs) -∗
      ⌜om_live_tids id locale_enabled (tp, σ) δ'⌝.
  Proof using.
    iIntros "HEAP MSI POSTS".
    rewrite /om_live_tids. iIntros (τ OBτ).
    rewrite /locale_enabled.
    red in OBτ.
    destruct (ps_obls δ' !! τ) as [V| ] eqn:OB_; [| done].
    simpl in OBτ.
    red in TH_OWN. rewrite set_eq in TH_OWN. specialize (TH_OWN τ).
    apply proj2 in TH_OWN. specialize (TH_OWN ltac:(eapply elem_of_dom; eauto)).
    apply locales_of_cfg_Some in TH_OWN as [e Ee]. simpl in Ee.
    iExists _. iSplit; [done| ].
    destruct (language.to_val e) eqn:VALe; [| done].
    apply from_locale_lookup in Ee.
    iDestruct (posts_of_empty_mapping_multiple with "[POSTS]") as "foo"; eauto.
    iDestruct (obls_msi_exact with "MSI foo") as %OB.
    rewrite OB_ in OB. congruence.
  Qed.

  Lemma no_obls_live_tids {Σ: gFunctors} {Hinv: @heapGS Σ M EM}
    (oGS := @heap_fairnessGS Σ _ _ Hinv)
    (tp : list expr) (σ : state) (δ' : ProgressState) ee
    (TH_OWN : threads_own_obls (tp, σ) δ'):
    gen_heap_interp (heap σ) -∗ obls_msi δ' (oGS := oGS) -∗
      cur_posts tp ee (λ _ : val, obls 0 ∅ (oGS := oGS)) -∗
      ⌜om_live_tids id locale_enabled (tp, σ) δ'⌝.
  Proof using.
    iIntros "HEAP MSI POSTS".
    rewrite /om_live_tids. iIntros (τ OBτ).
    rewrite /locale_enabled.
    red in OBτ.
    destruct (ps_obls δ' !! τ) as [V| ] eqn:OB_; [| done].
    simpl in OBτ.
    red in TH_OWN. rewrite set_eq in TH_OWN. specialize (TH_OWN τ).
    apply proj2 in TH_OWN. specialize (TH_OWN ltac:(eapply elem_of_dom; eauto)).
    apply locales_of_cfg_Some in TH_OWN as [e Ee]. simpl in Ee.
    iExists _. iSplit; [done| ].
    destruct (language.to_val e) eqn:VALe; [| done].
    apply from_locale_lookup in Ee.
    iDestruct (posts_of_empty_mapping with "[POSTS]") as "foo"; eauto.
    iDestruct (obls_msi_exact with "MSI foo") as %OB.
    rewrite OB_ in OB. congruence.
  Qed.

  (* TODO: move *)
  Lemma prefixes_simpl {A: Type} (es tp: list expr) (P: nat -> gset SignalId -> A): 
    ((λ '(tnew, e) (_ : val), P (locale_of tnew e) ∅) <$> prefixes_from es (drop (length es) tp)) = (map (fun i _ => P i ∅) (seq (length es) (length tp - length es))). 
  Proof using.
    destruct (decide (length es < length tp)).
    2: { rewrite skipn_all2; [| lia].
         replace (length tp - length es) with 0.
         { done. }
         simpl in n. lia. }

    remember (drop (length es) tp) as tp'.
    replace (length tp - length es) with (length tp').
    2: { subst. rewrite length_drop. lia. }
    clear Heqtp'. simpl.

    clear l. revert es. 

    induction tp'.
    { simpl. done. }

    intros. simpl.
    f_equal.
    pose proof (IHtp' (es ++ [a])).
    replace (S (length es)) with (length (es ++ [a])).
    2: { simpl. rewrite length_app. simpl. lia. } 
    rewrite -H2. simpl. done.
  Qed.    

  (* TODO: generalize? *)
  Lemma om_sim_RAH_multiple
          {Σ: gFunctors} {Hinv: @heapGS Σ M EM}
    σ1 es (* ds eb *) δ
    (LIVE0: om_live_tids id locale_enabled (es, σ1) δ) :
  ⊢
  rel_always_holds  NotStuck
    (map (fun i v => em_thread_post i%nat v (em_GS0 := (@heap_fairnessGS Σ
            _
            _ Hinv))) (seq 0 (length es)))
    (@obls_sim_rel)
    (es, σ1)
    (* (@init_om_state _ _ _ LIM_STEPS OP (es, σ1) ds eb) *)
    δ
  .
  Proof using.
    rewrite /rel_always_holds.
    
    iIntros (extr omtr [tp σ] VALID EX0 OM0 EX_FIN CONT_SIM).
    simpl. iIntros (NSTUCK FOOBAR).
    iIntros "(%VALID_STEP & HEAP & MSI & [%TH_OWN %OBLS]) POSTS".
    
    iApply fupd_mask_intro_discard; [done| ].
    
    clear CONT_SIM.

    destruct extr.
    { iPureIntro.
      simpl in VALID_STEP.
      inversion VALID. subst.
      red in EX0, OM0. simpl in EX0, OM0. subst.
      rewrite /obls_sim_rel. rewrite /valid_state_evolution_fairness /om_live_tids.
      split; [done| ]. simpl. red.
      (* apply om_live_tids_init. *)
      apply LIVE0. 
    }

    (* Unset Printing Notations. *)

    rewrite prefixes_simpl.
    rewrite -map_app. rewrite -seq_app.
    rewrite -Nat.le_add_sub. 
 
    simpl in VALID_STEP. inversion VALID. subst. simpl in *.
    red in EX_FIN. simpl in EX_FIN. subst. simpl.
    rewrite /obls_sim_rel. iSplit.
    { simpl. iPureIntro. red.
      destruct ℓ. done. }
    simpl. rewrite /obls_st_rel.

    iApply (no_obls_live_tids_multiple with "[$] [$]"); try done.
    eapply valid_exec_length.
    { eapply valid_system_trace_valid_exec_trace; eauto. }
    all: eauto.
  Qed.

  (* TODO: generalize? *)
  Lemma om_sim_RAH
          {Σ: gFunctors} {Hinv: @heapGS Σ M EM}
    σ1 e ds eb:
  ⊢
  rel_always_holds0
    (@obls_sim_rel) NotStuck
    (@state_interp heap_lang _ Σ _)
    (λ v : language.val heap_lang,
       @em_thread_post heap_lang _ _ Σ
         (@heap_fairnessGS Σ
            _
            _ Hinv) 0 v) e σ1
    (@init_om_state _ _ _ LIM_STEPS OP ([e], σ1) ds eb).
  Proof using.
    rewrite /rel_always_holds0.
    
    iIntros (extr omtr [tp σ] VALID EX0 OM0 EX_FIN CONT_SIM).
    simpl. iIntros (NSTUCK FOOBAR).
    iIntros "(%VALID_STEP & HEAP & MSI & [%TH_OWN %OBLS]) POSTS".
    
    iApply fupd_mask_intro_discard; [done| ].
    
    clear CONT_SIM.

    destruct extr.
    { iPureIntro.
      simpl in VALID_STEP.
      inversion VALID. subst.
      red in EX0, OM0. simpl in EX0, OM0. subst.
      rewrite /obls_sim_rel. rewrite /valid_state_evolution_fairness /om_live_tids.
      split; [done| ]. simpl. red.
      apply om_live_tids_init. }
 
    simpl in VALID_STEP. inversion VALID. subst. simpl in *.
    red in EX_FIN. simpl in EX_FIN. subst. simpl.
    rewrite /obls_sim_rel. iSplit.
    { simpl. iPureIntro. red.
      destruct ℓ. done. }
    simpl. rewrite /obls_st_rel.

    iApply (no_obls_live_tids with "[$] [$] [$]"). done.
  Qed.

  (* TODO: move *)
  Lemma indexes_seq {A: Type} (l: list A):
    indexes l = seq 0 (length l).
  Proof using.
    rewrite /indexes. rewrite imap_seq_0. by rewrite list_fmap_id.
  Qed.

  Lemma obls_match_impl_multiple Σ
    {HEAP: @heapGpreS Σ M EM}
    (extr : heap_lang_extrace) (es: list expr) (σ: state)
    (* (cps_degs: gmultiset Degree) (eb: nat) *)
    (* (s1 := init_om_state (trfirst extr) cps_degs eb (OP := OP)) *)
    δ
    (Hexfirst : trfirst extr = (es, σ))
    (LEN: length es ≥ 1)
    (OM_INIT: obls_is_init_st (es, σ) δ)
    (LIVE0: om_live_tids id locale_enabled (es, σ) δ)
    (WPe: forall (HEAP: @heapGS Σ M EM), ⊢ (([∗ map] l↦v ∈ heap σ, l ↦ v) ∗
                                     (@em_init_resource heap_lang M EM Σ (@heap_fairnessGS Σ M EM HEAP) δ tt))%I -∗
            let Φs := map (fun τ v => @em_thread_post heap_lang M EM Σ (@heap_fairnessGS Σ M EM HEAP) τ v) (seq 0 (length es)) in
              wptp NotStuck es Φs)
    (VALID: extrace_valid extr)
    :
    ∃ omtr, exec_OM_traces_match extr omtr ∧ om_tr_wf omtr /\ trfirst omtr = δ. 
  Proof.
    forward eapply om_simulation_adequacy_model_trace_multiple; eauto.
    - apply obls_sim_rel_FB. 
    - red. intros ?. iStartProof. iIntros "[HEAP INIT] !>".
      set (hGS := {| heap_iemgs := Hinv |}). 
      iPoseProof (WPe hGS with "[$HEAP $INIT]") as "foo".
      iSplitR; [| iSplitL]. 
      + by iApply hl_config_wp.
      + simpl. simpl in WPe.
        by rewrite locales_of_list_indexes indexes_seq.
      + rewrite locales_of_list_indexes indexes_seq.
        by iApply om_sim_RAH_multiple.
    - intros (?&?&?).
      rewrite -H3.
      opose proof * (obls_matching_traces_OM) as (omtr & COND); eauto.
      { rewrite H3. eapply obls_init_wf. eauto. }
      exists omtr. split_and !; apply COND. 
  Qed.

  Lemma obls_match_impl Σ
    `{HEAP: @heapGpreS Σ M EM}
    (extr : heap_lang_extrace) (e: expr) (σ: state)
    (cps_degs: gmultiset Degree) (eb: nat)
    (s1 := init_om_state (trfirst extr) cps_degs eb (OP := OP))
    (Hexfirst : trfirst extr = ([e], σ))
    (WPe: forall (HEAP: @heapGS Σ M EM), ⊢ (([∗ map] l↦v ∈ heap σ, l ↦ v) ∗
                                     (@em_init_resource heap_lang M EM Σ (@heap_fairnessGS Σ M EM HEAP) s1 tt))%I -∗
            (WP e @locale_of [] e {{ v, @em_thread_post heap_lang M EM Σ (@heap_fairnessGS Σ M EM HEAP) 0 v}})%I)
    (VALID: extrace_valid extr)
    :
    ∃ omtr, exec_OM_traces_match extr omtr ∧ om_tr_wf omtr /\ trfirst omtr = s1. 
  Proof.
    eapply obls_match_impl_multiple; eauto.
    { subst s1. rewrite Hexfirst. apply init_om_state_init. } 
    { subst s1. rewrite Hexfirst. apply om_live_tids_init. } 
    iIntros "**".
    simpl. iSplit; [| done].
    by iApply WPe.
  Qed.

  Lemma obls_terminates_impl_multiple Σ
    {HEAP: @heapGpreS Σ M EM}
    (extr : heap_lang_extrace) (es: list expr) (σ: state)
    (* (cps_degs: gmultiset Degree) (eb: nat)     *)
    (* (s1 := init_om_state (trfirst extr) cps_degs eb (OP := OP)) *)
    δ
    (Hexfirst : trfirst extr = (es, σ))
    (LEN: length es >= 1)
    (OM_INIT: obls_is_init_st (es, σ) δ)
    (LIVE0: om_live_tids id locale_enabled (es, σ) δ)
    (WPe: forall (HEAP: @heapGS Σ M EM), ⊢ (([∗ map] l↦v ∈ heap σ, l ↦ v) ∗
                                     (@em_init_resource heap_lang M EM Σ (@heap_fairnessGS Σ M EM HEAP) δ tt))%I
            ={⊤}=∗
            let Φs := map (fun τ v => @em_thread_post heap_lang M EM Σ (@heap_fairnessGS Σ M EM HEAP) τ v) (seq 0 (length es)) in
              wptp NotStuck es Φs)
    :
    extrace_fairly_terminating extr.
  Proof.
    unshelve epose proof (simple_om_simulation_adequacy_terminate_multiple Σ NotStuck
                  _ _ _ _
                  _ _ Hexfirst) as FAIR_TERM; eauto.
    { exact tt. }
    
    apply FAIR_TERM; auto. 
    red. intros ?. iStartProof. iIntros "[HEAP INIT]".
    set (hGS := {| heap_iemgs := Hinv |}). 
    iPoseProof (WPe hGS with "[$HEAP $INIT]") as "foo".
    rewrite locales_of_list_indexes indexes_seq.
    iSplitR; [| iSplitL].
    - by iApply hl_config_wp.
    - done. 
    - iApply om_sim_RAH_multiple. eauto. 
  Qed.

  Lemma obls_terminates_impl Σ
    {HEAP: @heapGpreS Σ M EM}
    (extr : heap_lang_extrace) (e: expr) (σ: state)
    (cps_degs: gmultiset Degree) (eb: nat)    
    (s1 := init_om_state (trfirst extr) cps_degs eb (OP := OP))
    (Hexfirst : trfirst extr = ([e], σ))
    (WPe: forall (HEAP: @heapGS Σ M EM), ⊢ (([∗ map] l↦v ∈ heap σ, l ↦ v) ∗
                                     (@em_init_resource heap_lang M EM Σ (@heap_fairnessGS Σ M EM HEAP) s1 tt))%I -∗
            (WP e @locale_of [] e {{ v, @em_thread_post heap_lang M EM Σ (@heap_fairnessGS Σ M EM HEAP) 0 v}})%I)
    :
    extrace_fairly_terminating extr.
  Proof.
    eapply obls_terminates_impl_multiple; eauto.
    { subst s1. rewrite Hexfirst. apply init_om_state_init. } 
    { subst s1. apply om_live_tids_init. }
    iIntros "**". simpl. iModIntro. iSplit; [| done].
    subst s1. rewrite -Hexfirst. by iApply WPe. 
  Qed.

  Local Existing Instance OP. 

  Lemma closed_pre_helper {Σ: gFunctors} {oGS: ObligationsGS Σ}
          (e: expr) (k: nat) (d: Degree) (σ: state) (b: nat):
    obls_init_resource (init_om_state ([e], σ) (k *: {[+ d +]}) b) ()  ⊢
      th_phase_eq (locale_of [] e) (ext_phase π0 0)  ∗
      cp_mul (ext_phase π0 0) d k ∗ obls (locale_of [] e) ∅.
  Proof using.
    iIntros "INIT". 
    rewrite /obls_init_resource /init_om_state.
    rewrite init_phases_helper. simpl.
    rewrite locales_of_cfg_simpl. simpl.
    iDestruct "INIT" as "(CPS & SIGS & OB & EPS & PH & EB)".
    rewrite union_empty_r_L !gset_to_gmap_singleton.
    rewrite big_sepM_singleton. iFrame.
    rewrite mset_map_mul.
    iApply cp_mul_weaken.
    { apply phase_lt_fork. }
    { reflexivity. }
    rewrite cp_mul_alt mset_map_singleton. done.     
  Qed.

  Lemma empty_obls_helper `{!ObligationsGS Σ} (T: gset (locale heap_lang)):
  @own Σ _
           (@obls_pre_obls _ _ _ _ OP _ _)
           (@obls_obls _ _ _ _ OP _ _)
           (◯ (Excl <$> @gset_to_gmap nat _ _ _ ∅ T)) -∗
    [∗ set] τ ∈ T, obls τ ∅.
  Proof using.
    clear. 
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

End OblsAdequacy.
