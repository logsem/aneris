From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import locales_helpers comp_utils trace_lookup fairness fin_branch.
From trillium.fairness.heap_lang Require Import simulation_adequacy.
From trillium.fairness.lawyer Require Import sub_action_em action_model.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_em obls_fairness_preservation obligations_am obligations_fin_branch obls_termination multiset_utils.
From trillium.fairness.lawyer.examples.eo_fin Require Import eo_fin.
From trillium.fairness.lawyer.examples Require Import bounded_nat.


Section EOFinAdequacy.

  Context (LIM: nat).
  Let OP := EO_OP LIM. 
  Let ASEM := ObligationsASEM OP.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} τ => obls OP τ ∅ (H3 := aGS)).
  Let OM := ObligationsModel OP. 
  Let M := AM2M (ObligationsAM OP). 
  
  Definition eofin_valid_evolution_step (c1 : cfg heap_lang) (oζ : olocale heap_lang) 
    (c2 : cfg heap_lang) (δ1 : mstate M) (ℓ : mlabel M) (δ2 : mstate M): Prop :=
    obls_ves_wrapper OP c1 oζ c2 δ1 ℓ δ2. 

  Definition eofin_st_rel (c: cfg heap_lang) (δ: mstate M) :=
    om_live_tids OP id locale_enabled c δ. 
    
  Definition eofin_sim_rel (extr: execution_trace heap_lang) (omtr: auxiliary_trace M) :=
    valid_state_evolution_fairness eofin_valid_evolution_step extr omtr ∧
    eofin_st_rel (trace_last extr) (trace_last omtr).

  Definition eofin_om_traces_match: extrace heap_lang -> trace (mstate M) (mlabel M) -> Prop :=
    traces_match
      (fun oτ '(_, τ') => oτ = τ')
      eofin_st_rel
      locale_step
      (@mtrans M).

  Lemma eofin_sim_rel_FB: rel_finitary eofin_sim_rel.
  Proof using.
    clear. red. intros extr mtr [tp' σ'] oζ. 
    simpl. rewrite /eofin_sim_rel. simpl.
    rewrite /eofin_valid_evolution_step /eofin_st_rel. simpl.
    apply list_approx_smaller_card. 
    apply OM_fin_branch_impl; try by apply _.
  Qed. 
    
  Theorem om_simulation_adequacy_model_trace Σ
        `{hPre: !heapGpreS Σ EM} (s: stuckness)
        (e1: expr) σ1 (s1: mstate M) p
        (INIT: em_is_init_st ([e1], σ1) s1 (ExecutionModel := EM))
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : trfirst extr = ([e1], σ1))    :
    wp_premise Σ s e1 σ1 s1 eofin_sim_rel (p: @em_init_param _ _ EM) ->
    ∃ (omtr: trace (mstate M) (mlabel M)), 
      eofin_om_traces_match extr omtr ∧
      trfirst omtr = s1.
  Proof using.
    (* clear H1 H0 H.  *)
    intros (* FIN *) PREM.

    unshelve epose proof (@strong_simulation_adequacy_traces _ _ _ hPre s e1 σ1
                s1
                eofin_sim_rel
                p
                extr
                Hvex
                ltac:(done)
                eofin_valid_evolution_step
                eofin_st_rel
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
    { apply eofin_sim_rel_FB. }
    { done. }
    { done. }

    done. 
  Qed.

  Lemma eofin_matching_traces_termination extr mtr
    (VALID: extrace_valid extr)
    (OM_WF0: om_st_wf _ (trfirst mtr))
    (FAIR: ∀ tid, fair_ex tid extr)
    (MATCH: eofin_om_traces_match extr mtr)
    (LIM_NZ: 0 < LIM):
  terminating_trace extr.
  Proof using.
    clear -MATCH FAIR VALID OM LIM_NZ OM_WF0.
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

    (* TODO: extract these lemmas *)
    assert (out_om_traces_match OP locale_step Some
              (fun oτ c => from_option (fun τ => locale_enabled τ c) False oτ)
              extr omtr) as MATCH''.
    { eapply trace_utils.traces_match_impl; [..| apply MATCH'].
      - simpl. intros ?? ([??] & <- & ?). done.
      - simpl. intros ?? (? & ? & ?). subst. eauto. } 
    assert (∀ ζ, out_fair (λ oτ c,
                     from_option (λ τ, locale_enabled τ c) False oτ) ζ extr) as FAIR''.
    { intros oζ. red. simpl. clear -FAIR.
      apply fair_by_equiv. red. intros n EN. simpl in EN.
      destruct (extr S!! n) eqn:NTH; rewrite NTH in EN; [| done]. 
      simpl in EN. 
      destruct oζ as [ζ | ]; [| done]. 
      simpl in EN. simpl.
      specialize (FAIR ζ). apply fair_by_equiv in FAIR.
      red in FAIR. specialize (FAIR n ltac:(by rewrite NTH)).
      destruct FAIR as (?&?&?&FAIR).
      do 2 eexists. split; eauto.
      destruct FAIR as [| FAIR]. 
      { left. done. }
      right. destruct FAIR as (?&?&?). eauto. }
    pose proof (out_om_fairness_preserved _ _ _ _ _ extr omtr MATCH'' FAIR'') as OM_FAIR. 

    pose proof (traces_match_valid2 _ _ _ _ _ _ MATCH'') as OM_VALID.  
    pose proof (obls_fair_trace_terminate _ _ OM_VALID OM_FAIR) as OM_TERM.
    specialize_full OM_TERM.
    { intros. eapply pres_by_valid_trace with (i := 0) (j := i) in OM_VALID. 
      2: apply wf_preserved_by_loc_step.
      2: apply wf_preserved_by_fork_step.
      2: { rewrite state_lookup_0. simpl.
           apply traces_match_first in MATCHo.
           by rewrite -MATCHo. }
      2: lia.
      by rewrite H in OM_VALID. }
    { apply fin_wf. }
    { apply fin_wf. }
    { constructor. by exists 0. }
    
    pose proof (traces_match_preserves_termination _ _ _ _ _ _ MATCH'' OM_TERM). 
    done.
  Qed. 
  
  
  Theorem simple_om_simulation_adequacy_terminate Σ
        (* `{hPre: !heapGpreS Σ EM} (s: stuckness) *)
        (* (e1: expr) σ1 (s1: mstate OM) (* p *) *)
        (* (INIT: obls_is_init_st OP ([e1], σ1) s1) *)
        (* (extr : heap_lang_extrace) *)
        (* (Hexfirst : trfirst extr = ([e1], σ1))    : *)
        `{hPre: !heapGpreS Σ EM} (s: stuckness)
        (e1: expr) σ1 (s1: mstate M) p
        (INIT: em_is_init_st ([e1], σ1) s1 (ExecutionModel := EM))
        (extr : heap_lang_extrace)
        (* (Hvex : extrace_valid extr) *)
        (Hexfirst : trfirst extr = ([e1], σ1))
        (LIM_NZ: 0 < LIM):
    (* rel_finitary (sim_rel LM) → *)
    wp_premise Σ s e1 σ1 s1 eofin_sim_rel (p: @em_init_param _ _ EM) -> 
    extrace_fairly_terminating extr.
  Proof.
    rewrite /extrace_fairly_terminating.
    intros (* Hterm Hfb *) Hwp (* VALID *) VALID FAIR.

    destruct (om_simulation_adequacy_model_trace
                Σ _ e1 _ s1 _ INIT _ VALID Hexfirst Hwp) as (omtr&MATCH&OM0).

    eapply eofin_matching_traces_termination; eauto.
    rewrite OM0.
    simpl in INIT. red in INIT. set_solver. 
  Qed.


  Let eofinΣ: gFunctors := #[
      GFunctor (excl_authR natO); 
      GFunctor (authUR (gmapUR nat (agreeR SignalId)));
      heapΣ EM
  ].

  Global Instance subG_eofinΣ {Σ}: subG eofinΣ Σ → EoFinPreG Σ.
  Proof. solve_inG. Qed.


  (* TODO: move *)
  Lemma om_live_tids_init e σ ds eb:
      om_live_tids OP id locale_enabled ([e], σ) (init_om_state (EO_OP LIM) ([e], σ) ds eb).
  Proof using. 
    red. intros ?.
    rewrite /has_obls. simpl. 
    rewrite locales_of_cfg_simpl. simpl. rewrite union_empty_r_L.
    rewrite gset_to_gmap_singleton. 
    destruct (decide (ζ = 0)) as [-> | ?].
    2: { simpl. simpl. rewrite lookup_singleton_ne; [| done]. done. }
    by rewrite lookup_singleton.
  Qed.

  Lemma no_obls_live_tids
          {Hinv: @heapGS eofinΣ M EM}
          (oGS := @heap_fairnessGS eofinΣ _ _ Hinv)
    (tp : list expr)
  (σ : state)
  (δ' : ProgressState OP)
  ee
  (TH_OWN : threads_own_obls OP (tp, σ) δ'):
  gen_heap_interp (heap σ) -∗ obls_msi OP δ' (H3 := oGS) -∗
  cur_posts tp ee (λ _ : val, obls OP 0 ∅ (H3 := oGS)) -∗
  ⌜om_live_tids OP id locale_enabled (tp, σ) δ'⌝.
  Proof using.
    clear -Hinv TH_OWN.
    iIntros "HEAP MSI POSTS".
    rewrite /om_live_tids. iIntros (τ OBτ).
    rewrite /locale_enabled.
    red in OBτ.
    destruct (ps_obls _ δ' !! τ) as [V| ] eqn:OB_; [| done].
    simpl in OBτ.
    red in TH_OWN. rewrite set_eq in TH_OWN. specialize (TH_OWN τ).
    apply proj2 in TH_OWN. specialize (TH_OWN ltac:(eapply elem_of_dom; eauto)).
    apply locales_of_cfg_Some in TH_OWN as [e Ee]. simpl in Ee.
    iExists _. iSplit; [done| ].
    destruct (language.to_val e) eqn:VALe; [| done].
    apply from_locale_lookup in Ee.
    iDestruct (posts_of_empty_mapping with "[POSTS]") as "foo"; eauto.
    simpl.
    iDestruct (obls_msi_exact with "MSI foo") as %?.
    clear -OB_ OBτ H. rewrite OB_ in H. congruence.
  Qed. 

  Lemma om_sim_RAH 
    {Hinv: @heapGS eofinΣ M EM}
    σ1 N ds eb:
  ⊢
  rel_always_holds0 
    (@eofin_sim_rel) NotStuck
    (@state_interp heap_lang _ eofinΣ _)
    (λ _ : language.val heap_lang,
       @em_thread_post heap_lang _ _ eofinΣ
         (@heap_fairnessGS eofinΣ
            _
            _ Hinv) 0) (start #0 #N) σ1
    (@init_om_state _ _ _ _ _ 10 (EO_OP LIM) ([start #0 #N], σ1) ds eb).
  Proof using.
    rewrite /rel_always_holds0.
    
    iIntros (extr omtr [tp σ] VALID EX0 OM0 EX_FIN CONT_SIM).
    simpl. iIntros (NSTUCK FOOBAR).
    iIntros "(%VALID_STEP & HEAP & MSI & [%TH_OWN %OBLS]) POSTS".
    
    iApply fupd_mask_intro_discard; [done| ].
    
    destruct extr.
    { iPureIntro.  
      simpl in VALID_STEP.
      inversion VALID. subst. 
      red in EX0, OM0. simpl in EX0, OM0. subst.
      rewrite /eofin_sim_rel. rewrite /valid_state_evolution_fairness /om_live_tids.
      split; [done| ]. simpl. red.
      apply om_live_tids_init. }
    simpl in VALID_STEP. inversion VALID. subst. simpl in *.
    red in EX_FIN. simpl in EX_FIN. subst. simpl.
    rewrite /eofin_sim_rel. iSplit.
    { simpl. iPureIntro. red. 
      destruct ℓ. done. }
    simpl. rewrite /eofin_st_rel.

    iApply (no_obls_live_tids with "[$] [$] [$]"). done.  
  Qed.

  Lemma eofin_terminates_impl
    (N : nat)
    (HN: N > 1)
    (LIM_NZ: N < LIM)
    (extr : heap_lang_extrace)
    (Hexfirst : (trfirst extr).1 = [start #(0%nat) #N]):
    (* (∀ tid, fair_ex tid extr) -> terminating_trace extr. *)
    extrace_fairly_terminating extr. 
  Proof.
    assert (heapGpreS eofinΣ EM) as HPreG.
    { apply _. }

    destruct (trfirst extr) as [tp_ σ1] eqn:EX0. simpl in *. subst tp_.
    
    set (s1 := init_om_state (EO_OP LIM) (trfirst extr)
               ((2 * N + 5) *: {[+ d2 +]} ⊎ 50 *: {[+ d0 +]})
                 20
        ). 
    
    unshelve epose proof (simple_om_simulation_adequacy_terminate eofinΣ NotStuck
                  _ _ _ _
                  _ _ EX0) as FAIR_TERM; eauto.
    { exact tt. }
    { simpl. subst s1. rewrite EX0.
      apply init_om_state_init. }
    
    apply FAIR_TERM.
    { lia. }
    red. intros ?. iStartProof. iIntros "[HEAP INIT] !>".
    iSplitL.
    - simpl. 
      iApply (main_spec with "[-]"); try done.
      5: { simpl. iNext. iIntros (_) "X". iApply "X". }
      3: { simpl. iIntros (? _) "X". iApply "X". }
      { apply AMU_lift_top. }
      { intros. rewrite /AMU_lift_MU__f.
        rewrite -nclose_nroot.
        apply AMU_lift_top. }
      rewrite /obls_init_resource. subst s1. simpl.
      rewrite EX0.
      rewrite init_phases_helper. 
      rewrite locales_of_cfg_simpl. simpl.
      rewrite union_empty_r_L. simpl. 
      iDestruct "INIT" as "(CPS & SIGS & OB & EPS & PH & EB)".
      rewrite /cps_repr /sig_map_repr /eps_repr /phases_repr /obls_map_repr. 
      rewrite map_fmap_singleton fmap_empty.
      rewrite !gset_to_gmap_singleton. 
      rewrite map_fmap_singleton.      
      iFrame.
      rewrite !bi.sep_assoc. iSplitR "PH". 
      2: { iExists _.
           rewrite /phases_repr. rewrite map_fmap_singleton. iFrame.
           iPureIntro. apply phase_lt_fork. }
      rewrite mset_map_disj_union.
      rewrite auth_frag_op.
      iDestruct (own_op with "CPS") as "[CPS2 CPS0]".
      iSplitL "CPS2".
      + rewrite /cp_mul.
        iApply (own_mono with "[$]").
        apply auth_frag_mono.
        rewrite mset_map_mul mset_map_singleton.
        apply gmultiset.gmultiset_included. 
        apply scalar_mul_le. lia.
      + iApply (own_mono with "CPS0").
        apply auth_frag_mono.
        rewrite mset_map_mul mset_map_singleton.
        apply gmultiset.gmultiset_included. 
        apply scalar_mul_le. lia.
    - subst s1. rewrite EX0. iApply om_sim_RAH. 
  Qed. 

End EOFinAdequacy.

(* TODO: try to get rid of N restriction *)
Theorem eofin_terminates N (N1: 1 < N):
  forall extr,
    (trfirst extr).1 = [start #0%nat #N] → 
    extrace_fairly_terminating extr.
Proof using.
  intros.
  eapply eofin_terminates_impl with (LIM := N + 1); eauto.
  lia.
Qed. 
