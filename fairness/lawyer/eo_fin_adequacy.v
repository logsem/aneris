From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import locales_helpers.
From trillium.fairness.heap_lang Require Import simulation_adequacy.
From trillium.fairness.lawyer Require Import obligations_model obligations_resources.
From trillium.fairness.lawyer Require Import eo_fin. 


(* TODO: unify defs *)
Definition extrace_fairly_terminating' {Λ} `{Countable (locale Λ)}
           (extr : extrace Λ) :=
  extrace_valid extr →
  (∀ tid, fair_ex tid extr) →
  terminating_trace extr.



Section OMTermination.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Context `{Countable Locale}. 
  Let OM := ObligationsModel OP. 

  Definition has_obls (τ: Locale) (s: mstate OM) := default ∅ (ps_obls _ s !! τ) ≠ ∅. 

  Definition obls_trace_fair := fair_by has_obls eq.

  Definition obls_trace_valid := trace_valid (@mtrans OM).

  Definition obls_trace := trace (mstate OM) (mlabel OM). 

  Lemma obls_fair_trace_terminate (tr: obls_trace):
    obls_trace_valid tr ->
    (∀ τ, obls_trace_fair τ tr) ->
    terminating_trace tr.
  Proof. Admitted. 

  (* Definition live_rel (ex : execution_trace Λ) (aux : auxiliary_trace (fair_model_model LM_Fair)) := *)
  (* live_tids (LM:=LM) (trace_last ex) (trace_last aux). *)

  (* Definition sim_rel (ex : execution_trace Λ) (aux : auxiliary_trace (fair_model_model LM_Fair)) := *)
  (*   valid_state_evolution_fairness lm_valid_evolution_step ex aux (M := (fair_model_model LM_Fair)) ∧ live_rel ex aux. *)

  (* Definition sim_rel_with_user (ξ : execution_trace Λ -> finite_trace M (option (fmrole M)) -> Prop) *)
  (* (ex : execution_trace Λ) (aux : auxiliary_trace (fair_model_model LM_Fair)) := *)
  (* sim_rel ex aux ∧ ξ ex (get_underlying_fairness_trace aux). *)

End OMTermination.


Section ObligationsAdequacy.

  Context {DegO LevelO: ofe}.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO} `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}.
  Context {LIM_STEPS: nat}.

  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context (OP: ObligationsParams Degree Level (locale heap_lang) LIM_STEPS).
  Let OM := ObligationsModel OP.

  (* Context `{hGS: @heapGS Σ _ EM}. *)
  (* Let oGS : ObligationsGS EO_OP Σ := heap_fairnessGS (heapGS := hGS). *)

  Let EM := @ObligationsEM DegO LevelO _ _ _ heap_lang _ _ _ OP.

  Definition om_live_tids (c: cfg heap_lang) (δ: mstate OM) :=
    forall ζ, (default ∅ (ps_obls _ δ !! ζ) ≠ ∅) -> locale_enabled ζ c.

  Definition ex_om_traces_match: extrace heap_lang -> obls_trace OP -> Prop :=
    traces_match
      (fun oτ τ' => oτ = Some τ')
      om_live_tids
      locale_step
      (@mtrans OM).

  Lemma ex_om_fairness_preserved (extr: extrace heap_lang) (omtr: obls_trace OP):
    ex_om_traces_match extr omtr ->
    (forall ζ, fair_ex ζ extr) -> (∀ τ, obls_trace_fair _ τ omtr).
  Proof using. Admitted. 


  Definition om_sim_rel (extr: execution_trace heap_lang) (omtr : auxiliary_trace OM) :=
    valid_state_evolution_fairness (obls_valid_evolution_step OP) extr omtr ∧
    om_live_tids (trace_last extr) (trace_last omtr). 

  Lemma om_sim_rel_FB: rel_finitary om_sim_rel.
  Proof. Admitted. 

  Theorem om_simulation_adequacy_model_trace Σ
        `{hPre: !heapGpreS Σ EM} (s: stuckness)
        (e1: expr) σ1 (s1: mstate OM) (* p *)
        (INIT: obls_is_init_st OP ([e1], σ1) s1)
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : trfirst extr = ([e1], σ1))    :
    wp_premise Σ s e1 σ1 s1 om_sim_rel (tt: @em_init_param _ _ EM) ->
    ∃ (omtr: obls_trace OP), 
      ex_om_traces_match extr omtr ∧
      trfirst omtr = s1.
  Proof using.
    intros (* FIN *) PREM.

    unshelve epose proof (@strong_simulation_adequacy_traces _ _ _ hPre s e1 σ1
                s1
                om_sim_rel
                tt
                extr
                Hvex
                ltac:(done)
                (obls_valid_evolution_step OP)
                om_live_tids
                (fun oτ τ' => oτ = Some τ')
                _ _ _ _ _ _ _
      ) as SIM.
    { simpl. intros ?????? STEP. apply STEP. }
    { simpl. intros ?????? STEP. apply STEP. }
    { simpl. intros ?? SIM. apply SIM. }
    { simpl. intros ?? SIM. apply SIM. }
    { apply om_sim_rel_FB. }
    { done. }
    { done. }

    done. 
  Qed.

  Theorem simple_om_simulation_adequacy_terminate Σ
        `{hPre: !heapGpreS Σ EM} (s: stuckness)
        (e1: expr) σ1 (s1: mstate OM) (* p *)
        (INIT: obls_is_init_st OP ([e1], σ1) s1)
        (extr : heap_lang_extrace)
        (Hexfirst : trfirst extr = ([e1], σ1))    :
    (* rel_finitary (sim_rel LM) → *)
    wp_premise Σ s e1 σ1 s1 om_sim_rel (tt: @em_init_param _ _ EM) -> 
    extrace_fairly_terminating' extr.
  Proof.
    rewrite /extrace_fairly_terminating'. 
    intros (* Hterm Hfb *) Hwp VALID FAIR.    

    destruct (om_simulation_adequacy_model_trace
                Σ _ e1 _ s1 INIT _ VALID Hexfirst Hwp) as (omtr&MATCH&OM0).

    have OM_FAIR := ex_om_fairness_preserved extr omtr MATCH FAIR.
    pose proof (traces_match_valid2 _ _ _ _ _ _ MATCH) as OM_VALID.  
    pose proof (obls_fair_trace_terminate _ _ OM_VALID OM_FAIR) as OM_TERM. 
    pose proof (traces_match_preserves_termination _ _ _ _ _ _ MATCH OM_TERM). 
    done. 
  Qed.

  (* TODO: move *)
  Definition phase0: Phase := nroot .@ "phases". 

  (* TODO: move *)
  Definition init_phases (n: nat): list Phase :=
    (fun i => phase0 .@ i) <$> seq 0 n. 

  (* TODO: move *)
  Definition init_om_state (c: cfg heap_lang): mstate OM := {|
      ps_cps := ∅;
      ps_sigs := ∅;
      ps_obls := gset_to_gmap ∅ (locales_of_cfg c);
      ps_eps := ∅;
      ps_phases := list_to_map $ zip (elements $ locales_of_cfg c) (init_phases (size $ locales_of_cfg c));
      ps_exc_bound := 1;
  |}.

  (* TODO: move *)
  Lemma init_om_thown (c: cfg heap_lang):
    threads_own_obls _ c (init_om_state c).
  Proof.
    red. simpl. by rewrite dom_gset_to_gmap.
  Qed.

  (* TODO: move *)
  Lemma length_size `{Countable K} (g: gset K):
    length (elements g) = size g.
  Proof.
    rewrite -{2}(list_to_set_elements_L g).
    rewrite size_list_to_set; [done| ]. apply NoDup_elements.
  Qed.

  Lemma init_om_dpo (c: cfg heap_lang):
    dom_phases_obls _ (init_om_state c).
  Proof.
    red. simpl. rewrite dom_list_to_map_L. simpl.
    rewrite fst_zip.
    { by rewrite list_to_set_elements_L dom_gset_to_gmap. }
    rewrite /init_phases. rewrite fmap_length.
    rewrite seq_length. rewrite length_size. lia.
  Qed. 
  
  Lemma init_om_state_init e σ:
    obls_is_init_st _ ([e], σ) (init_om_state (([e], σ))).
  Proof.
    red. eexists. split.
    { rewrite locales_of_cfg_simpl. simpl. rewrite union_empty_r_L. reflexivity. }
    rewrite dom_gset_to_gmap. split.
    { rewrite locales_of_cfg_simpl. simpl. rewrite union_empty_r_L. reflexivity. }
    rewrite dom_list_to_map_L.
    rewrite fst_zip.
    { rewrite list_to_set_elements_L. rewrite locales_of_cfg_simpl.
      simpl. rewrite union_empty_r_L. reflexivity. } 
    rewrite /init_phases. rewrite (fmap_length _ (seq _ _)) seq_length.
    lia.
  Qed.     
    
End ObligationsAdequacy.


Section EOFinAdequacy.

  Context (LIM: nat). 

  Let EM := EO_EM LIM.

  Let eofinΣ: gFunctors := #[
      GFunctor (excl_authR natO); 
      GFunctor (authUR (gmapUR nat (agreeR SignalId)));
      heapΣ EM
].

  Global Instance subG_eofinΣ {Σ}: subG eofinΣ Σ → EoFinPreG Σ.
  Proof. solve_inG. Qed.

  (* TODO: move*)
  Lemma gset_to_gmap_singleton `{Countable K} {B: Type} (b: B) (k: K):
    gset_to_gmap b {[ k ]} = {[ k := b ]}.
  Proof.
    rewrite /gset_to_gmap. simpl. rewrite map_fmap_singleton. done.
  Qed. 

  Lemma locales_of_cfg_Some τ tp σ:
    τ ∈ locales_of_cfg (tp, σ) -> is_Some (from_locale (tp, σ).1 τ).
  Proof.
    rewrite /locales_of_cfg. simpl. rewrite elem_of_list_to_set.
    apply locales_of_list_from_locale_from'.
  Qed.

  Lemma om_sim_RAH 
    {Hinv: @heapGS eofinΣ (ObligationsModel (EO_OP LIM)) EM}
    σ1 N:
  ⊢
  rel_always_holds0 
    (@om_sim_rel _ _ 10 (EO_OP LIM)) NotStuck
    (@state_interp heap_lang _ eofinΣ _)
    (λ _ : language.val heap_lang,
       @em_thread_post heap_lang _ _ eofinΣ
         (@heap_fairnessGS eofinΣ
            _
            _ Hinv) 0) (start #N) σ1
    (@init_om_state _ _ 10 (EO_OP LIM) ([start #N], σ1)).
  Proof using.
    rewrite /rel_always_holds0.
    
    iIntros (extr omtr [tp σ] VALID EX0 OM0 EX_FIN CONT_SIM).
    simpl. iIntros (NSTUCK FOOBAR).
    iIntros "(%VALID_STEP & HEAP & MSI & [%TH_OWN %OBLS]) POSTS".
    
    iApply fupd_mask_intro_discard; [done| ].
    
    destruct extr.
    { simpl in VALID_STEP. inversion VALID.
      simpl in *. subst. simpl in *.
      red in EX0. simpl in EX0. subst.
      red in OM0. simpl in OM0. subst.
      red in EX_FIN. simpl in EX_FIN. inversion EX_FIN. subst.
      simpl in VALID. simpl.
      rewrite /om_sim_rel. rewrite /valid_state_evolution_fairness /om_live_tids.
      iSplit; [done| ]. simpl.
      rewrite locales_of_cfg_simpl. simpl. rewrite union_empty_r_L.
      iPureIntro. intros ?.
      rewrite gset_to_gmap_singleton. 
      destruct (decide (ζ = 0)) as [-> | ?].
      2: { simpl. simpl. rewrite lookup_singleton_ne; [| done]. done. }
      by rewrite lookup_singleton. }
    simpl in VALID_STEP. inversion VALID. subst. simpl in *.
    red in EX_FIN. simpl in EX_FIN. subst. simpl.
    rewrite /om_sim_rel. iSplit.
    { simpl. done. }
    simpl. rewrite /om_live_tids. iIntros (τ OBτ).
    rewrite /locale_enabled.
    destruct (ps_obls _ δ' !! τ) as [V| ] eqn:OB_; rewrite OB_ in OBτ; [| done].
    simpl in OBτ.
    red in TH_OWN. rewrite set_eq in TH_OWN. specialize (TH_OWN τ).
    apply proj2 in TH_OWN. specialize (TH_OWN ltac:(eapply elem_of_dom; eauto)).
    apply locales_of_cfg_Some in TH_OWN as [e Ee]. simpl in Ee.
    iExists _. iSplit; [done| ].
    destruct (language.to_val e) eqn:VALe; [| done].
    apply from_locale_lookup in Ee. 
    iDestruct (posts_of_empty_mapping with "[POSTS]") as "foo"; eauto.
    simpl. iDestruct (obls_msi_exact with "MSI [$]") as %?.
    clear -OB_ OBτ H. rewrite OB_ in H. congruence.
    Unshelve. apply foo. 
  Qed. 
      

  Theorem eofin_terminates
    (N : nat)
    (HN: N > 1)
    (extr : heap_lang_extrace)
    (Hexfirst : (trfirst extr).1 = [start #N]):
    (* (∀ tid, fair_ex tid extr) -> terminating_trace extr. *)
    extrace_fairly_terminating' extr. 
  Proof.
    assert (heapGpreS eofinΣ EM) as HPreG.
    { apply _. }

    destruct (trfirst extr) as [tp_ σ1] eqn:EX0. simpl in *. subst tp_.                
    
    (* assert (mstate (ObligationsModel (EO_OP LIM))) as s1. *)
    (* { admit. } *)
    (* assert (obls_is_init_st (EO_OP LIM) ([start #N], σ1) s1) as INIT. *)
    (* { admit. } *)
    set (s1 := init_om_state (EO_OP LIM) (trfirst extr)). 
    
    unshelve epose proof (simple_om_simulation_adequacy_terminate (EO_OP LIM) eofinΣ NotStuck
                  _ _ _ _
                  _ EX0) as FAIR_TERM.
    2: { apply init_om_state_init. }
    apply FAIR_TERM.

    red. intros ?. iStartProof. iIntros "[HEAP INIT] !>".
    iSplitL.
    - admit.
    - iApply om_sim_RAH. 
  Admitted. 

End EOFinAdequacy.
