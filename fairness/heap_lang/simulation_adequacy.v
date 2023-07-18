From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre adequacy.
From trillium.fairness Require Export fairness resources fair_termination fairness_finiteness fuel fuel_termination.
From trillium.fairness.heap_lang Require Export lang heap_lang_defs.


Section adequacy.

(* Local Hint Resolve tid_step_tp_length_heap: core. *)

Theorem heap_lang_continued_simulation_fair_termination {FM : FairModel}
        `{FairTerminatingModel FM} {LM:LiveModel heap_lang FM} ξ a1 r1 extr :
  continued_simulation
    (sim_rel_with_user LM ξ)
    ({tr[trfirst extr]}) ({tr[initial_ls (LM := LM) a1 r1]}) →
  extrace_fairly_terminating extr.
Proof.
  apply continued_simulation_fair_termination.
  - intros ?? contra. inversion contra.
    simplify_eq. inversion H2.
  - by intros ex atr [[??]?].
  - by intros ex atr [[??]?].
Qed.

Definition LM_init_resource `{LM:LiveModel heap_lang Mdl} `{!fairnessGS LM Σ}
  (s1: fmstate Mdl)
  (* FR *)
  : iProp Σ :=
  frag_model_is s1 ∗
  (∃ FR, frag_free_roles_are (FR ∖ live_roles _ s1)) ∗
  has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (Mdl.(live_roles) s1)). 

Definition init_thread_post `{LM:LiveModel heap_lang M} `{!fairnessGS LM Σ}
  (tid: locale heap_lang): iProp Σ :=
  tid ↦M ∅.


Global Instance LM_EM `{LM: LiveModel heap_lang M}: @ExecutionModel LM :=
  {|
    em_preGS := fun Σ => fairnessGpreS LM Σ;
    em_GS := fun Σ => fairnessGS LM Σ;
    em_Σ := fairnessΣ heap_lang M;
    em_Σ_subG := fun Σ => @subG_fairnessGpreS _ _ _ LM _ _;

    em_valid_state_evolution_fairness := valid_state_evolution_fairness;
    em_thread_post Σ := fun {_: fairnessGS LM Σ} (tid: locale heap_lang) (_: val) => tid ↦M ∅;
    (* TODO: cannot express the msi instantiation this way*)
    em_msi Σ := fun {_: fairnessGS LM Σ} es δ => model_state_interp es δ;                                                                                    
    em_init_resource Σ := fun {_: fairnessGS LM Σ} δ => LM_init_resource δ;
|}.

(* TODO: get rid of it*)
Global Instance LM_EM_fairPre `{LM: LiveModel heap_lang M}
                `{hGS: @heapGpreS Σ LM (@LM_EM _ LM)}:
  fairnessGpreS LM Σ.
Proof. apply hGS. Defined. 

(* TODO: get rid of it*)
Global Instance LM_EM_fair `{LM: LiveModel heap_lang M}
                `{hGS: @heapGS Σ LM (@LM_EM _ LM)}:
  fairnessGS LM Σ.
Proof. apply hGS. Defined. 

(* TODO: how to make 'heap..' instantiations less wordy? *)
Lemma init_fairnessGS_LM Σ `(LM:LiveModel heap_lang M)
  `{hPre: @heapGpreS Σ LM (@LM_EM _ LM)}
  (s1: M) (e1 : expr):
  ⊢ (|==> ∃ fGS: fairnessGS LM Σ, (* TODO: what is a canonical way of doing it? *)
       ∀ `{hGS: @heapGS Σ _ (@LM_EM _ LM)},
         ⌜ hGS.(heap_fairnessGS) = fGS⌝ →
      LM_init_resource s1 ∗ model_state_interp [e1] (initial_ls s1 0%nat (LM := LM))).
Proof.
  iIntros.
  iMod (model_state_init s1) as (γmod) "[Hmoda Hmodf]".
  iMod (model_mapping_init s1) as (γmap) "[Hmapa Hmapf]".
  iMod (model_fuel_init s1) as (γfuel) "[Hfuela Hfuelf]".
  (* TODO: seems like the concrete set of free roles doesn't matter *)
  (* iMod (model_free_roles_init s1 (FR ∖ live_roles _ s1)) as (γfr) "[HFR Hfr]". *)
  iMod (model_free_roles_init s1 ∅) as (γfr) "[HFR Hfr]".
  iModIntro.
  iExists ({|
              fairness_model_name := γmod;
              fairness_model_mapping_name := γmap;
              fairness_model_fuel_name := γfuel;
              fairness_model_free_roles_name := γfr;
            |}).
  iIntros.

  iSplitL "Hmodf Hfr Hfuelf Hmapf".
  2: { unfold model_state_interp. simpl. iFrame. 
       iExists {[ 0%nat := (live_roles M s1) ]}, _.
       iSplitL "Hfuela"; first by rewrite /auth_fuel_is /= fmap_gset_to_gmap //.
       iSplitL "Hmapa"; first by rewrite /auth_mapping_is /= map_fmap_singleton //.
       iSplit; first done.
       iSplit; iPureIntro; [|split].
       - intros ρ tid. rewrite lookup_gset_to_gmap_Some.
         setoid_rewrite lookup_singleton_Some. split; naive_solver.
       - intros tid Hlocs. rewrite lookup_singleton_ne //. compute in Hlocs. set_solver.
       - rewrite dom_gset_to_gmap. set_solver. }

  rewrite /LM_init_resource.
  rewrite /has_fuels /frag_mapping_is /= map_fmap_singleton.
    
  (* iFrame. *)
  iSplitL "Hmodf".
  { by rewrite /frag_model_is. }
  iSplitL "Hfr".
  { rewrite /frag_free_roles_are. 
    iExists ∅. rewrite subseteq_empty_difference_L; set_solver. }

  rewrite !dom_gset_to_gmap. iFrame.
  unfold frag_fuel_is.
  setoid_rewrite map_fmap_singleton. simpl.
  destruct (decide (live_roles M s1 = ∅)) as [-> | NE].
  { by iApply big_sepS_empty. }
  iDestruct (own_proper with "Hfuelf") as "Hfuelf".
  { apply auth_frag_proper. apply @gset_to_gmap_singletons. } 
  rewrite big_opS_auth_frag. rewrite big_opS_own; [| done].
  iApply (big_sepS_mono with "Hfuelf"). iIntros (ρ Hin) "H".
  iExists _. iFrame. iPureIntro. apply lookup_gset_to_gmap_Some. done.
Qed.

(* Lemma foo  `(LM:LiveModel heap_lang M) `{hGS: @heapGS Σ LM (@LM_EM _ LM)}: *)
(*   irisG heap_lang LM Σ. *)
(* apply _.  *)
(* Qed.  *)

Let rel_always_holds `{LM:LiveModel heap_lang M} `{hGS: @heapGS Σ LM (@LM_EM _ LM)}
  s ξ e1 σ1 δ1 := 
      rel_always_holds0 (fun etr atr => ξ etr (map_underlying_trace atr)) 
        s (state_interp) (fun _ => 0%nat ↦M ∅) e1 σ1 δ1. 

Lemma rel_always_holds_lift_LM `{LM: LiveModel heap_lang M} `{hGS: @heapGS Σ LM (@LM_EM _ LM)}
  s e1 σ1 s1 ξ:
  rel_always_holds s ξ e1 σ1 (initial_ls s1 0%nat) -∗
  rel_always_holds0 (sim_rel_with_user LM ξ) s state_interp
    (λ _, 0%nat ↦M ∅) e1 σ1 (initial_ls s1 0%nat).
Proof.
  iIntros "H".
  iIntros (ex atr c Hvalex Hstartex Hstartatr Hendex Hcontr Hstuck Hequiv) "Hsi Hposts".
  assert ( ∀ (ex' : finite_trace (cfg heap_lang) (olocale heap_lang)) (atr' : auxiliary_trace LM) (oζ : olocale heap_lang) (ℓ : mlabel LM),
   trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' (map_underlying_trace atr')) as Hcontr'.
  { intros ex' atr' oζ ℓ H1 H2. cut (sim_rel_with_user LM ξ ex' atr'); eauto. rewrite /sim_rel_with_user. intros [??]. done. }
  iSpecialize ("H" $! ex atr c Hvalex Hstartex Hstartatr Hendex Hcontr' Hstuck Hequiv).
  
  unfold sim_rel_with_user.
  iAssert (|={⊤}=> ⌜ξ ex (map_underlying_trace atr)⌝ ∗ state_interp ex atr ∗ posts_of c.1
               ((λ _ : language.val heap_lang, 0%nat ↦M ∅)
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
               ls_mapping (initial_ls (LM := LM) s1 0%nat) !! ρ = Some tid →
               is_Some (([e1], σ1).1 !! tid)) as HA.
    { simpl. intros ρ tid Hsome. apply lookup_gset_to_gmap_Some in Hsome as [??].
      simplify_eq. by eexists _. }
    iSplit; last done. iClear "H1".
    iSplit; first done.
    destruct (to_val e1) as [v1|] eqn:Heq.
    + iSplit.
      { iPureIntro. intros ρ tid Hinit.
        simpl in *. apply lookup_gset_to_gmap_Some in Hinit as [_ <-].
        rewrite /from_locale //. }
      iIntros (tid e Hsome Hnoval ρ). destruct tid; last done.
      simpl in Hsome. compute in Hsome. simplify_eq. simpl.
      iAssert (0%nat ↦M ∅) with "[Hposts]" as "Hem".
      { rewrite /= Heq /fmap /=. by iDestruct "Hposts" as "[??]". }
      iDestruct "Hsi" as "(_&_&Hsi)".
      iDestruct "Hsi" as "(%m&%FR'&Hfuela&Hmapa&HFR&%Hinvmap&%Hsmall&Hmodel&HfrFR)".
      iDestruct (frag_mapping_same 0%nat m with "[Hmapa] Hem") as "%H"; [done| ].
      iPureIntro. by eapply no_locale_empty.
    + iSplit; iPureIntro.
      { simpl. intros ρ tid Hsome. apply lookup_gset_to_gmap_Some in Hsome as [??].
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
    iDestruct "Hsi" as "((%&%&%Htids)&_&Hsi)".
    iDestruct "Hsi" as "(%m&%&Hfuela&Hmapa&?&%Hinvmap&%Hsmall&Hmodel&?)".
    iSplit; [|done].
    iSplit; [done|].
    iSplit.
    + iPureIntro. intros ρ tid' Hsome. simpl. unfold tids_smaller in Htids. eapply Htids. done.
    + iIntros (tid' e' Hsome Hnoval ρ). simpl.
      iAssert (tid' ↦M ∅) with "[Hposts]" as "H".
      { destruct (to_val e') as [?|] eqn:Heq; last done.
        iApply posts_of_empty_mapping => //.
        apply from_locale_lookup =>//. }
      iDestruct (frag_mapping_same tid' m with "Hmapa H") as "%Hlk".
      { rewrite /auth_mapping_is. iPureIntro. by eapply no_locale_empty. }
Qed. 

Theorem strong_simulation_adequacy_general Σ `(LM:LiveModel heap_lang M)
    `{hPre: @heapGpreS Σ LM (@LM_EM _ LM)} (s: stuckness) (e1 : expr) σ1 (s1: M)
    (R: execution_trace heap_lang → auxiliary_trace LM → Prop)
  :
  rel_finitary R →
  (∀ `{Hinv : @heapGS Σ _ (@LM_EM _ LM)} ,
    ⊢ |={⊤}=>
       ([∗ map] l ↦ v ∈ heap σ1, mapsto l (DfracOwn 1) v) ∗
       LM_init_resource s1
       ={⊤}=∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ v, init_thread_post 0%nat }} ∗
       rel_always_holds0 R s state_interp (λ _, 0%nat ↦M ∅) e1 σ1 (initial_ls s1 0%nat)) ->
  continued_simulation R (trace_singleton ([e1], σ1)) (trace_singleton (initial_ls (LM := LM) s1 0%nat)).
Proof.
  intros Hfin H.
  apply (wp_strong_adequacy heap_lang LM Σ s); first by eauto.
  iIntros (?) "".

  iMod (gen_heap_init (heap σ1)) as (genheap)" [Hgen [Hσ _]]".  
  iMod (init_fairnessGS_LM _ _ s1 e1) as (fGS) "GEN".   

  set (distG := {| heap_fairnessGS := (fGS: (em_GS Σ (ExecutionModel := @LM_EM _ LM))) |}).
  iMod (H distG) as "Hwp". clear H.
  iSpecialize ("GEN" $! distG eq_refl). iDestruct "GEN" as "[LM_INIT MSI]".

  iExists state_interp, (λ _, 0%nat ↦M ∅)%I, fork_post.
  iSplitR.
  { unfold config_wp. iIntros "!>!>" (???????) "?". done. }
  iSpecialize ("Hwp" with "[Hσ LM_INIT]"); [by iFrame| ]. 
  iDestruct "Hwp" as ">[Hwp H]". 
  iModIntro. iFrame.
Qed.


Theorem strong_simulation_adequacy Σ `(LM:LiveModel heap_lang M)
    `{hPre: @heapGpreS Σ LM (@LM_EM _ LM)} (s: stuckness) (e1 : expr) σ1 (s1: M)
    (ξ : execution_trace heap_lang → finite_trace M (option $ fmrole M) →
         Prop) :
  rel_finitary (sim_rel_with_user LM ξ) →
  (∀ `{hGS: @heapGS Σ LM (@LM_EM _ LM)}, 
    ⊢ |={⊤}=>
       ([∗ map] l ↦ v ∈ heap σ1, mapsto l (DfracOwn 1) v) ∗
         LM_init_resource s1
       ={⊤}=∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ v, init_thread_post 0%nat }} ∗
       rel_always_holds s ξ e1 σ1 (initial_ls (LM := LM) s1 0%nat)) ->
  continued_simulation (sim_rel_with_user LM ξ) (trace_singleton ([e1], σ1)) (trace_singleton (initial_ls (LM := LM) s1 0%nat)).
Proof.
  intros Hfin WP_RAH.
  eapply strong_simulation_adequacy_general.
  1, 2: by eauto.
  iIntros. iModIntro. 
  iIntros "R". iMod (WP_RAH with "R") as ">[WP RAH]".
  iModIntro. iSplitL "WP"; [by iFrame| ]. 
  by iApply rel_always_holds_lift_LM. 
Qed.

Theorem simulation_adequacy Σ `(LM:LiveModel heap_lang M) `{hPre: @heapGpreS Σ LM (@LM_EM _ LM)} (s: stuckness) (e1 : expr) σ1 (s1: M):
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  (* The initial configuration satisfies certain properties *)
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{hGS: @heapGS Σ LM (@LM_EM _ LM)},
      ⊢ |={⊤}=>
         LM_init_resource s1
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, init_thread_post 0%nat }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  @continued_simulation
    heap_lang
    LM
    (sim_rel LM)
    (trace_singleton ([e1], σ1))
    (trace_singleton (initial_ls (LM := LM) s1 0%nat)).
Proof.
  intros Hne H.
  assert (sim_rel LM = sim_rel_with_user LM (λ _ _, True)) as Heq.
  { Require Import Coq.Logic.FunctionalExtensionality.
    Require Import Coq.Logic.PropExtensionality.
    do 2 (apply functional_extensionality_dep; intros ?).
    apply propositional_extensionality.
    unfold sim_rel_with_user. intuition. }

  rewrite Heq.
  apply (strong_simulation_adequacy Σ LM s) =>//.
  { rewrite -Heq. done. }
  iIntros (Hinv) "".
  iPoseProof (H Hinv) as ">H". iModIntro. iIntros "[Hσ (Hm & Hfr & Hf)]". iSplitR "".
  - iApply ("H" with "[Hm Hfr Hf]"). rewrite /LM_init_resource. iFrame. 
  - iIntros "!>%%%?????????".
    iApply (fupd_mask_weaken ∅); first set_solver. by iIntros "_ !>".
Qed.

Theorem simulation_adequacy_inftraces Σ `(LM: LiveModel heap_lang M)
        `{hPre: @heapGpreS Σ LM (@LM_EM _ LM)}  (s: stuckness)
        e1 σ1 (s1: M)
        (iex : inf_execution_trace heap_lang)
        (Hvex : valid_inf_exec (trace_singleton ([e1], σ1)) iex)
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM)  →
  (∀ `{hGS: @heapGS Σ LM (@LM_EM _ LM)},
      ⊢ |={⊤}=> LM_init_resource s1
         ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, init_thread_post 0%nat }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  exists iatr,
  @valid_inf_system_trace _ LM
    (@continued_simulation
       heap_lang
       LM
       (sim_rel LM))
    (trace_singleton ([e1], σ1))
    (trace_singleton (initial_ls (LM := LM) s1 0%nat))
    iex
    iatr.
Proof.
  intros Hfin Hwp.
  eexists.
  eapply produced_inf_aux_trace_valid_inf.
  Unshelve.
  - econstructor.
  - apply (simulation_adequacy Σ LM s) => //.
  - done.
Qed.

Definition heap_lang_extrace : Type := extrace heap_lang.

Theorem simulation_adequacy_traces Σ `(LM : LiveModel heap_lang M)
  `{hPre: @heapGpreS Σ LM (@LM_EM _ LM)} (s: stuckness)
        e1 (s1: M)
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  (∀ `{hGS: @heapGS Σ LM (@LM_EM _ LM)},
      ⊢ |={⊤}=> LM_init_resource s1
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, init_thread_post 0%nat }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  ∃ (auxtr : auxtrace LM), exaux_traces_match extr auxtr.
Proof.
  intros Hfin Hwp.
  have [iatr Hbig] : exists iatr,
      @valid_inf_system_trace
        heap_lang LM
        (@continued_simulation
           heap_lang
           LM
           (sim_rel LM))
        (trace_singleton ([e1], (trfirst extr).2))
        (trace_singleton (initial_ls (LM := LM) s1 0%nat))
        (from_trace extr)
        iatr.
  { apply (simulation_adequacy_inftraces _ _ s); eauto.
    eapply from_trace_preserves_validity; eauto; first econstructor.
    simpl. destruct (trfirst extr) eqn:Heq.
    simpl in Hexfirst. rewrite -Hexfirst Heq //. }
  exists (to_trace (initial_ls (LM := LM) s1 0%nat) iatr).
  eapply (valid_inf_system_trace_implies_traces_match (continued_simulation (sim_rel LM))); eauto.
  - by intros ? ? [? ?]%continued_simulation_rel.
  - by intros ? ? [? ?]%continued_simulation_rel.
  - apply from_trace_spec. simpl. destruct (trfirst extr) eqn:Heq. simplify_eq. f_equal.
    simpl in Hexfirst. rewrite -Hexfirst Heq //.
  - apply to_trace_spec.
Qed.


Theorem simulation_adequacy_model_trace Σ `(LM : LiveModel heap_lang M)
        `{hPre: @heapGpreS Σ LM (@LM_EM _ LM)} (s: stuckness)
        e1 (s1: M)
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  (∀ `{hGS: @heapGS Σ LM (@LM_EM _ LM)},
      ⊢ |={⊤}=> LM_init_resource s1 ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, init_thread_post 0%nat }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  ∃ (auxtr : auxtrace LM) mtr, exaux_traces_match extr auxtr ∧
                               upto_stutter ls_under Ul auxtr mtr.
Proof.
  intros Hfb Hwp.
  destruct (simulation_adequacy_traces
              Σ _ _ e1 s1 extr Hvex Hexfirst Hfb Hwp) as [auxtr Hmatch].
  assert (auxtrace_valid auxtr) as Hstutter.
  { by eapply exaux_preserves_validity in Hmatch. }
  destruct (can_destutter_auxtr auxtr) as [mtr Hupto] =>//.
  eauto.
Qed.
  

Theorem simulation_adequacy_terminate Σ `{LM:LiveModel heap_lang Mdl}
        `{hPre: @heapGpreS Σ LM (@LM_EM _ LM)} (s: stuckness)
        e1 (s1: Mdl)
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (∀ mtr: @mtrace Mdl, mtrace_fairly_terminating mtr) ->
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  (∀ `{hGS: @heapGS Σ LM (@LM_EM _ LM)},
      ⊢ |={⊤}=> LM_init_resource s1
                 ={⊤}=∗
                 WP e1 @ s; 0%nat; ⊤ {{ v, init_thread_post 0%nat }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  extrace_fairly_terminating extr.
Proof.  
  intros Hterm Hfb Hwp Hvex Hfair.
  destruct (simulation_adequacy_model_trace
              Σ _ _ e1 s1 extr Hvex Hexfirst Hfb Hwp) as (auxtr&mtr&Hmatch&Hupto).
  destruct (infinite_or_finite extr) as [Hinf|] =>//.
  have Hfairaux := fairness_preserved extr auxtr Hinf Hmatch Hfair.
  have Hvalaux := exaux_preserves_validity extr auxtr Hmatch.
  have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux.
  have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.
  have Htermtr := Hterm mtr Hmtrvalid Hfairm.
  eapply exaux_preserves_termination =>//.
  eapply upto_stutter_finiteness =>//.
Qed.

Theorem simulation_adequacy_terminate_ftm Σ `{FairTerminatingModel M}
        `(LM : LiveModel heap_lang M)
        `{hPre: @heapGpreS Σ LM (@LM_EM _ LM)} (s: stuckness)
        e1 (s1: M)
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  (∀ `{hGS: @heapGS Σ LM (@LM_EM _ LM)},
      ⊢ |={⊤}=> LM_init_resource s1 ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, init_thread_post 0%nat }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  extrace_fairly_terminating extr.
Proof.
  eapply simulation_adequacy_terminate =>//.
  apply fair_terminating_traces_terminate.
Qed.

End adequacy.
