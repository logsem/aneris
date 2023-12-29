From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fuel fuel_termination fairness_finiteness fair_termination_natural utils lm_fair lm_fair_traces lm_fairness_preservation traces_match.
From trillium.fairness.heap_lang Require Import lang simulation_adequacy em_lm_heap_lang em_lm.



Section adequacy.
(* Local Hint Resolve tid_step_tp_length_heap: core. *)
  Context `{LM: LiveModel (locale heap_lang) M LSI}.
  (* Context {LF: LMFairPre LM}.  *)
  Context {LF': LMFairPre' LM}. 

  Local Instance LF: LMFairPre LM.
  esplit; apply _.
  Defined. 

Theorem heap_lang_continued_simulation_fair_termination 
        `{FairTerminatingModel M}  ξ a1 r1 extr
        (LSI0: initial_ls_LSI a1 r1)
  :
  continued_simulation
    (sim_rel_with_user LM ξ)
    ({tr[trfirst extr]}) ({tr[initial_ls' a1 r1 LSI0]}) →
  extrace_fairly_terminating extr.
Proof.
  apply continued_simulation_fair_termination.
  - intros ?? contra. inversion contra.
    simplify_eq. inversion H2.
  - by intros ex atr [[??]?].
  - by intros ex atr [[??]?].
Qed.

Let rel_always_holds `{hGS: @heapGS Σ (fair_model_model LM_Fair) (@LM_EM_HL _ _ _ _LF)}
  s ξ e1 σ1 δ1 := 
      rel_always_holds0 (fun etr atr => ξ etr (get_underlying_fairness_trace atr)) 
        s (state_interp) (fun _ => frag_mapping_is {[ 0%nat := ∅ ]} (LM := LM)) e1 σ1 δ1. 


Lemma rel_always_holds_lift_LM 
  `{hGS: @heapGS Σ (fair_model_model LM_Fair) (@LM_EM_HL _ _ _ LF')}
  s e1 σ1 s1 ξ
  (LSI0: initial_ls_LSI s1 0):
  rel_always_holds s ξ e1 σ1 (initial_ls' s1 0%nat LSI0) -∗
  rel_always_holds0 (sim_rel_with_user LM ξ) s state_interp
    (λ _, frag_mapping_is {[ 0%nat := ∅ ]}) e1 σ1 (initial_ls' s1 0%nat LSI0).
Proof.
  iIntros "H".
  iIntros (ex atr c Hvalex Hstartex Hstartatr Hendex Hcontr Hstuck Hequiv) "Hsi Hposts".
  assert ( ∀ (ex' : finite_trace (cfg heap_lang) (olocale heap_lang)) (atr' : auxiliary_trace (fair_model_model LM_Fair)) (oζ : olocale heap_lang) ℓ,
   trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' (get_underlying_fairness_trace atr')) as Hcontr'.
  { intros ex' atr' oζ ℓ H1 H2. cut (sim_rel_with_user LM ξ ex' atr'); eauto. rewrite /sim_rel_with_user. intros [??]. done. }
  iSpecialize ("H" $! ex atr c Hvalex Hstartex Hstartatr Hendex Hcontr' Hstuck Hequiv).
  
  unfold sim_rel_with_user.
  iAssert (|={⊤}=> ⌜ξ ex (get_underlying_fairness_trace atr)⌝ ∗ state_interp ex atr ∗ posts_of c.1
               ((λ _ : language.val heap_lang, frag_mapping_is {[ 0%nat := ∅ ]})
                :: ((λ '(tnew, e), fork_post (language.locale_of tnew e)) <$>
                    prefixes_from [e1] (drop (length [e1]) c.1))))%I with "[Hsi H Hposts]" as "H".
  { iApply fupd_plain_keep_l. iFrame. iIntros "[Hsi Hposts]".
    iSpecialize ("H" with "Hsi Hposts").
    by iApply fupd_plain_mask_empty. }
  iMod "H" as "[H1 [Hsi Hposts]]".
  destruct ex as [c'|ex' tid (e, σ)].
  - (* We need to prove that the initial state satisfies the property *)
    destruct atr as [δ|???]; last by inversion Hvalex. simpl.
    have Heq1 := trace_singleton_ends_in_inv _ _ Hendex.
    have Heq3 := trace_singleton_starts_in_inv _ _ Hstartex.
    have Heq4 := trace_singleton_starts_in_inv _ _ Hstartex.
    pose proof (trace_singleton_starts_in_inv _ _ Hstartatr). simpl.
    simplify_eq.
    iApply (fupd_mask_weaken ∅); first set_solver. iIntros "_ !>".
    assert (∀ (ρ : fmrole M) (tid : nat),
               ls_mapping (initial_ls' (LM := LM) s1 0%nat LSI0) !! ρ = Some tid →
               is_Some (([e1], σ1).1 !! tid)) as HA.
    { simpl. rewrite initial_ls'_mapping. 
      setoid_rewrite lookup_gset_to_gmap_Some.
      intros ?? [? <-]. by eexists _. }
    iSplit; last done. iClear "H1".
    iSplit; first done.
    destruct (to_val e1) as [v1|] eqn:Heq.
    + iSplit.
      { iPureIntro. rewrite initial_ls'_mapping. intros ρ tid Hinit.
        simpl in *. apply lookup_gset_to_gmap_Some in Hinit as [_ <-].
        rewrite /from_locale //. }
      iIntros (tid e Hsome Hnoval ρ). destruct tid; last done.
      simpl in Hsome. compute in Hsome. simplify_eq. simpl.
      iAssert (frag_mapping_is {[ 0%nat := ∅ ]}) with "[Hposts]" as "Hem".
      { rewrite /= Heq /fmap /=. by iDestruct "Hposts" as "[??]". }
      iDestruct "Hsi" as "(_&_&Hsi&Haux)".
      iDestruct "Hsi" as "(%FR'&Hfuela&Hmapa&HFR&Hmodel&HfrFR)".
      iDestruct (frag_mapping_same 0%nat with "[Hmapa] Hem") as "%H"; [done| ].
      iPureIntro. eapply no_locale_empty; [| done].
      rewrite initial_ls'_mapping. rewrite build_LS_ext_spec_tmap.
      apply maps_inverse_match_exact. 
    + iSplit; iPureIntro.
      { simpl. rewrite initial_ls'_mapping. intros ρ tid Hsome.
        apply lookup_gset_to_gmap_Some in Hsome as [??].
        simplify_eq. by eexists _. }
      intros tid e Hsome Hval' ρ.
      destruct tid as [|tid]; rewrite /from_locale /= in Hsome; by simplify_eq.
  - (* We need to prove that that the property is preserved *)
    destruct atr as [|atr' ℓ δ]; first by inversion Hvalex.
    (* rewrite (trace_singleton_ends_in_inv _ _ Hendex); last exact unit. *)
    specialize (Hcontr ex' atr' tid ℓ).
    have H: trace_contract (trace_extend ex' tid (e, σ)) tid ex' by eexists.
    have H': trace_contract (trace_extend atr' ℓ δ) ℓ atr' by eexists.
    specialize (Hcontr H H') as Hvs. clear H H' Hcontr.
    (* destruct Hvalex as (Hlm & Hlt & Hts). *)
    have H: trace_ends_in ex' (trace_last ex') by eexists.
    have H': trace_ends_in atr' (trace_last atr') by eexists.
    iApply (fupd_mask_weaken ∅); first set_solver. iIntros "_ !>".
    apply (trace_singleton_ends_in_inv (L := unit)) in Hendex.
    simpl in *. simplify_eq.
    iDestruct "Hsi" as "((%&%&%Htids)&_&Hsi&Haux)".
    iDestruct "Hsi" as "(%&Hfuela&Hmapa&?&Hmodel&?)".
    iSplit; [|done].
    iSplit; [done|].
    iSplit.
    + iPureIntro. intros ρ tid' Hsome. simpl.      
      unfold tids_smaller' in Htids. eapply Htids.
      eapply mim_in_1; eauto. apply ls_mapping_tmap_corr. 
    + iIntros (tid' e' Hsome Hnoval ρ). simpl.
      iAssert (frag_mapping_is {[ tid' := ∅ ]}) with "[Hposts]" as "H".
      { destruct (to_val e') as [?|] eqn:Heq; last done.
        iApply (@posts_of_empty_mapping _ LM_EM_HL) => //. 
        apply from_locale_lookup =>//. }
      iDestruct (frag_mapping_same tid' (ls_tmap δ) with "Hmapa H") as "%Hlk".
      { rewrite /auth_mapping_is. iPureIntro. eapply no_locale_empty; [| done].
        apply ls_mapping_tmap_corr. }
Qed.
  
Definition wp_premise
  `{hPre: @heapGpreS Σ (fair_model_model LM_Fair) (@LM_EM_HL _ _ _ LF')}
  ξ σ1 e1 s1 s FR
  (LSI0: initial_ls_LSI s1 0)
  (δ0 := initial_ls' (LM := LM) s1 0%nat LSI0)
    := (∀ `{hGS: @heapGS Σ (fair_model_model LM_Fair) (@LM_EM_HL _ _ _ LF')}, 
    ⊢ (|={⊤}=>
       (* ([∗ map] l ↦ v ∈ heap σ1, mapsto l (DfracOwn 1) v) ∗ *)
         LM_init_resource 0%nat δ0 (FR ∖ dom (ls_fuel δ0))
       ={⊤}=∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ v, init_thread_post 0%nat }} ∗
       rel_always_holds s ξ e1 σ1 δ0)). 

Theorem strong_simulation_adequacy Σ
    `{hPre: @heapGpreS Σ (fair_model_model LM_Fair) (@LM_EM_HL _ _ _ LF')} (s: stuckness) (e1 : expr heap_lang) σ1 (s1: M) FR
    (ξ : execution_trace heap_lang → finite_trace M (option $ fmrole M) →
         Prop)    
  (LSI0: initial_ls_LSI s1 0)
  (δ0 := initial_ls' (LM := LM) s1 0%nat LSI0)
  :
  rel_finitary (sim_rel_with_user LM ξ) →
  (∀ `{hGS: @heapGS Σ (fair_model_model LM_Fair) (@LM_EM_HL _ _ _ LF')},
    ⊢ (|={⊤}=>
         ([∗ map] l ↦ v ∈ heap σ1, mapsto l (DfracOwn 1) v) ∗
         LM_init_resource 0%nat δ0 (FR ∖ dom (ls_fuel δ0))
       ={⊤}=∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ v, init_thread_post 0%nat }} ∗
       rel_always_holds s ξ e1 σ1 δ0))
  (* wp_premise conv_init ξ σ1 e1 s1 s LSI0 *)
 ->
  continued_simulation (sim_rel_with_user LM ξ) (trace_singleton ([e1], σ1)) (trace_singleton δ0).
Proof.
  intros Hfin WP_RAH.
  eapply @strong_simulation_adequacy_general.
  1,2,4: done.
  { split.
    - red. eauto.
    - red. split.
      + by rewrite build_LS_ext_spec_st build_LS_ext_spec_fuel.
      + by rewrite build_LS_ext_spec_tmap build_LS_ext_spec_st. } 
  iIntros (?) "INIT".
  iMod (WP_RAH Hinv) as "WP_RAH".
  iMod ("WP_RAH" with "INIT") as "[WP RAH]".
  iModIntro. iSplitL "WP"; [by iFrame| ]. 
  by iApply rel_always_holds_lift_LM. 
Qed.

Theorem simulation_adequacy Σ  `{hPre: @heapGpreS Σ (fair_model_model LM_Fair) (@LM_EM_HL _ _ _ LF')} (s: stuckness) (e1 : expr heap_lang) σ1 (s1: M) FR
  (LSI0: initial_ls_LSI s1 0)
  (δ0 := initial_ls' (LM := LM) s1 0%nat LSI0)
:
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  (* The initial configuration satisfies certain properties *)
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  wp_premise (λ _ _, True) σ1 e1 s1 s FR LSI0 ->
    (* The coinductive pure coq proposition given by adequacy *)
  @continued_simulation
    heap_lang
    (fair_model_model LM_Fair)
    (sim_rel LM)
    (trace_singleton ([e1], σ1))
    (trace_singleton δ0).
Proof.
  intros Hne H.
  assert (sim_rel LM = sim_rel_with_user LM (λ _ _, True)) as Heq.
  { Require Import Coq.Logic.FunctionalExtensionality.
    Require Import Coq.Logic.PropExtensionality.
    do 2 (apply functional_extensionality_dep; intros ?).
    apply propositional_extensionality.
    unfold sim_rel_with_user. intuition. }

  rewrite Heq.
  eapply (strong_simulation_adequacy Σ s) =>//.
  { rewrite -Heq. done. }
  iIntros (Hinv) "".
  iPoseProof (H Hinv) as "H_".

  iModIntro. iIntros "[Hσ INIT']".
  iMod ("H_" with "INIT'") as "H".
  done. 
Qed.

Theorem simulation_adequacy_inftraces Σ
        `{hPre: @heapGpreS Σ (fair_model_model LM_Fair) (@LM_EM_HL _ _ _ LF')}  (s: stuckness)
        e1 σ1 (s1: M) FR
        (LSI0: initial_ls_LSI s1 0)
        (iex : inf_execution_trace heap_lang)
        (Hvex : valid_inf_exec (trace_singleton ([e1], σ1)) iex)
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM)  →
  wp_premise (λ _ _, True) σ1 e1 s1 s FR LSI0 ->
  (* The coinductive pure coq proposition given by adequacy *)
  exists iatr,
  @valid_inf_system_trace _ (fair_model_model LM_Fair)
    (@continued_simulation
       heap_lang
       (fair_model_model LM_Fair)
       (sim_rel LM))
    (trace_singleton ([e1], σ1))
    (trace_singleton (initial_ls' (LM := LM) s1 0%nat LSI0))
    iex
    iatr.
Proof.
  intros Hfin Hwp.
  eexists.
  eapply produced_inf_aux_trace_valid_inf.
  Unshelve.
  - econstructor.
  - eapply (simulation_adequacy Σ s) => //.
  - done.
Qed.

Definition heap_lang_extrace : Type := extrace heap_lang.

(* TODO: move *)
Definition to_trace_trfirst {S L : Type}
  (s: S) (il: inflist (L * S)):
  trfirst (to_trace s il) = s.
Proof. 
  destruct il as [| [??]]; done.
Qed. 


(* TODO: derive from general case? *)
Theorem simulation_adequacy_traces Σ
  `{hPre: @heapGpreS Σ (fair_model_model LM_Fair) (@LM_EM_HL _ _ _ LF')} (s: stuckness)
        e1 (s1: M) FR
        (LSI0: initial_ls_LSI s1 0)
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  wp_premise (λ _ _, True) (trfirst extr).2 e1 s1 s FR LSI0 ->
  (* The coinductive pure coq proposition given by adequacy *)
  ∃ (auxtr : lmftrace (LM := LM)), 
    lm_exaux_traces_match extr auxtr (LM := LM) /\
    trfirst auxtr = initial_ls' s1 0 LSI0.
Proof.
  intros Hfin Hwp.
  have [iatr Hbig] : exists iatr,
      @valid_inf_system_trace
        heap_lang (fair_model_model LM_Fair)
        (@continued_simulation
           heap_lang
           (fair_model_model LM_Fair)
           (sim_rel LM))
        (trace_singleton ([e1], (trfirst extr).2))
        (trace_singleton (initial_ls' (LM := LM) s1 0%nat LSI0))
        (from_trace extr)
        iatr.
  { eapply (simulation_adequacy_inftraces _ s); eauto.
    eapply from_trace_preserves_validity; eauto; first econstructor.
    simpl. destruct (trfirst extr) eqn:Heq.
    simpl in Hexfirst. rewrite -Hexfirst Heq //. }
  exists (to_trace (initial_ls' (LM := LM) s1 0%nat LSI0) iatr).
  split.
  2: { by rewrite to_trace_trfirst. }
  
  unshelve eapply (valid_inf_system_trace_implies_traces_match (M := fair_model_model LM_Fair)
            lm_valid_evolution_step
            live_tids
            _
            ltac:(idtac)
            ltac:(idtac)
            (continued_simulation (sim_rel LM))); eauto.
  - intros ?????? [MATCH _].
    subst. by destruct ℓ. 
  - intros ?????? V; by apply V. 
  - by intros ? ? [? ?]%continued_simulation_rel.
  - by intros ? ? [? ?]%continued_simulation_rel.
  - apply from_trace_spec. simpl. destruct (trfirst extr) eqn:Heq. simplify_eq. f_equal.
    simpl in Hexfirst. rewrite -Hexfirst Heq //.
  - apply to_trace_spec.
Qed.


Theorem simulation_adequacy_model_trace Σ
        `{hPre: @heapGpreS Σ (fair_model_model LM_Fair) (@LM_EM_HL _ _ _ LF')} (s: stuckness)
        e1 (s1: M) FR
        (LSI0: initial_ls_LSI s1 0)
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  wp_premise (λ _ _, True) (trfirst extr).2 e1 s1 s FR LSI0 ->
  (* The coinductive pure coq proposition given by adequacy *)
  ∃ (auxtr : lmftrace (LM:=LM)) mtr, 
    lm_exaux_traces_match extr auxtr (LM := LM) ∧
    upto_stutter ls_under Usls auxtr mtr /\
    trfirst auxtr = initial_ls' s1 0 LSI0. 
Proof.
  intros Hfb Hwp.
  destruct (simulation_adequacy_traces
              Σ _ e1 s1 _ LSI0 extr Hvex Hexfirst Hfb Hwp) as (auxtr & Hmatch & A0).
  assert (mtrace_valid auxtr) as Hstutter.
  { by eapply traces_match_valid2 in Hmatch. }
  destruct (can_destutter_auxtr auxtr) as [mtr Hupto] =>//.
  eauto.
Qed.

Definition get_LF: LMFairPre' LM -> LMFairPre LM. 
intros. split; apply X. 
Defined. 

Theorem simulation_adequacy_terminate Σ
        `{hPre: @heapGpreS Σ (fair_model_model LM_Fair) (@LM_EM_HL _ _ _ LF')} (s: stuckness)
        e1 (s1: M) FR
        (LSI0: initial_ls_LSI s1 0)
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (∀ mtr: @mtrace M, trfirst mtr = s1 -> mtrace_fairly_terminating mtr) ->
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  wp_premise (λ _ _, True) (trfirst extr).2 e1 s1 s FR LSI0 ->
  (* The coinductive pure coq proposition given by adequacy *)
  extrace_fairly_terminating extr.
Proof.
  intros Hterm Hfb Hwp Hvex Hfair.

  destruct (simulation_adequacy_model_trace
              Σ _ e1 s1 _ LSI0 extr Hvex Hexfirst Hfb Hwp) as (auxtr&mtr&Hmatch&Hupto&A0).
  have Hfairaux := ex_fairness_preserved 
                     extr auxtr Hmatch Hfair.
  (* assert (LMFairPre LM) as LF. *)
  (* { esplit; apply LF'. } *)
  set LF := get_LF LF'.
  pose proof (proj1 (LM_ALM_afair_by_next LM auxtr) (Hfairaux LF)) as Hfairaux'. 
  have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux'.
  (* have Hvalaux := traces_match_LM_preserves_validity extr auxtr _ _ _ Hmatch. *)
  pose proof Hmatch as Hvalaux%traces_match_valid2. 
  have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.
  pose proof Hupto as M0%upto_stutter_trfirst. rewrite A0 in M0.  
  have Htermtr := Hterm mtr M0 Hmtrvalid Hfairm.
  eapply traces_match_preserves_termination =>//.
  eapply upto_stutter_finiteness =>//.
Qed.


Theorem simulation_adequacy_terminate_ftm Σ `{FairTerminatingModel M}
        `{hPre: @heapGpreS Σ (fair_model_model LM_Fair) (@LM_EM_HL _ _ _ LF')} (s: stuckness)
        e1 (s1: M) FR
        (LSI0: initial_ls_LSI s1 0)
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  wp_premise (λ _ _, True) (trfirst extr).2 e1 s1 s FR LSI0 ->
  (* The coinductive pure coq proposition given by adequacy *)
  extrace_fairly_terminating extr.
Proof.
  eapply simulation_adequacy_terminate =>//.
  intros ? _. 
  by apply fair_terminating_traces_terminate.
Qed.

Theorem simple_simulation_adequacy_terminate_ftm Σ `{FairTerminatingModelSimple M}
        `{!heapGpreS Σ (@LM_EM_HL _ _ _ LF')} (s: stuckness)
        e1 (s1: M) FR
        (LSI0: initial_ls_LSI s1 0)
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  wp_premise (λ _ _, True) (trfirst extr).2 e1 s1 s FR LSI0 -> 
  (* The coinductive pure coq proposition given by adequacy *)
  extrace_fairly_terminating extr.
Proof.
  intros. eapply simulation_adequacy_terminate =>//.
  intros ? _.
  by eapply simple_fair_terminating_traces_terminate.
Qed.

End adequacy.


Section adequacy_general.
Context `{CNT: Countable G}.
Context `{LM: LiveModel G M LSI}. 
Context {LF: LMFairPre LM}. 

Theorem simulation_adequacy_terminate_general'
  `{Mout: FairModel}
  (otr: mtrace Mout) (auxtr : lmftrace (LM := LM))
  state_rel lift_grole:
  (∀ mtr: @mtrace M, mtrace_fairly_terminating mtr) ->
  (* (forall ρ, fair_aux ρ auxtr (LM := LM)) -> *)
  (∀ ρ : fmrole M, fair_by_next_TS ρ auxtr) ->
  lm_model_traces_match lift_grole state_rel otr auxtr (transA := olocale_trans) (LM := LM) ->
  mtrace_fairly_terminating otr.
Proof.
  intros Hterm Hfairaux Hmatch.
  red. intros VALID FAIR. 

  pose proof Hmatch as Hvalaux%traces_match_valid2. 
  destruct (can_destutter_auxtr auxtr (LM := LM)) as [mtr Hupto] =>//.
  have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux.
  have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.
  have Htermtr := Hterm mtr Hmtrvalid Hfairm.
  eapply traces_match_preserves_termination =>//.
  eapply upto_stutter_finiteness =>//.
Qed.

(* TODO: unify with the language-oriented version above *)
Theorem simulation_adequacy_terminate_general
  `{Mout: FairModel}
  `{EqDecision G}
  (otr: mtrace Mout) (auxtr : lmftrace (LM := LM))
  state_rel lift_grole:
  (∀ mtr: @mtrace M, mtrace_fairly_terminating mtr) ->
  Inj eq eq lift_grole ->
  (forall i δ, auxtr S!! i = Some δ -> lm_live_lift (LM_ALM LM) (option_fmap _ _ lift_grole) (from_option (role_enabled_model (M := Mout)) (fun _ => False)) state_rel δ) ->
  (* lm_model_traces_match lift_grole state_rel otr auxtr -> *)
  lm_model_traces_match (option_fmap _ _ lift_grole) state_rel otr auxtr (transA := olocale_trans) (LM := LM) ->
  (* The coinductive pure coq proposition given by adequacy *)
  mtrace_fairly_terminating otr.
Proof.
  intros. red. intros.
  eapply simulation_adequacy_terminate_general'; eauto.
  intros. apply LM_ALM_afair_by_next.
  eapply model_fairness_preserved; eauto.
  apply _. 
Qed.

End adequacy_general.
