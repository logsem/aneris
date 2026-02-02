From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre adequacy.
From fairness Require Export fairness traces_match trace_utils.
From heap_lang Require Export lang heap_lang_defs.

Definition heap_lang_extrace : Type := extrace heap_lang.


Section adequacy.

  Definition wp_premise
    `{EM: ExecutionModel heap_lang M}
    (Σ: gFunctors)
    (s: stuckness) (e1 : expr) σ1 (s1: mstate M)
    (R: execution_trace heap_lang → auxiliary_trace M → Prop)
    (p: em_init_param)
    := 
    (∀ `{Hinv : @heapGS Σ M EM} ,
        ⊢ (([∗ map] l ↦ v ∈ heap σ1, pointsto l (DfracOwn 1) v) ∗
             em_init_resource s1 p (em_GS0 := heap_fairnessGS)
           ={⊤}=∗
              WP e1 @ s; locale_of [] e1; ⊤ {{ _, em_thread_post 0%nat (em_GS0 := heap_fairnessGS)}} ∗
                                            rel_always_holds0 R s state_interp (fun _ => em_thread_post 0%nat (em_GS0 := heap_fairnessGS)) e1 σ1 s1)). 

  Definition wp_premise_multiple
    `{EM: ExecutionModel heap_lang M}
    (Σ: gFunctors)
    (s: stuckness) es σ1 (s1: mstate M)
    (R: execution_trace heap_lang → auxiliary_trace M → Prop)
    (p: em_init_param)
    := 
    (∀ `{Hinv : @heapGS Σ M EM} ,
        ⊢ (([∗ map] l ↦ v ∈ heap σ1, pointsto l (DfracOwn 1) v) ∗
             em_init_resource s1 p (em_GS0 := heap_fairnessGS)
           ={⊤}=∗
              let Φs := map (fun i _ => em_thread_post i%nat (em_GS0 := heap_fairnessGS)) (seq 0 (length es)) in
              wptp s es Φs ∗
              rel_always_holds s Φs R (es, σ1) s1)).

  Lemma wp_premise_single `{EM: ExecutionModel heap_lang M} Σ
    s e1 σ1 s1 R p:
    wp_premise Σ s e1 σ1 s1 R p -> wp_premise_multiple Σ s [e1] σ1 s1 R p.
  Proof using.
    rewrite /wp_premise /wp_premise_multiple.
    iIntros "%WP1 % [HEAP INIT]".
    iMod (WP1 Hinv with "[$HEAP $INIT]") as "[WP1 RAH]".
    iFrame. set_solver.
  Qed.

  Theorem strong_simulation_adequacy_general_multiple
    `{hPre: @heapGpreS Σ M EM} (s: stuckness) (es : list expr) σ1 (s1: M)
    (R: execution_trace heap_lang → auxiliary_trace M → Prop)
    (p: em_init_param)    
    :
    length es ≥ 1 ->
    rel_finitary R →
    em_is_init_st (es, σ1) s1 ->
    em_valid_state_evolution_fairness {tr[ (es, σ1) ]} {tr[ s1 ]} ->
    (wp_premise_multiple Σ s es σ1 s1 R p) ->
    continued_simulation R (trace_singleton (es, σ1)) (trace_singleton s1).
  Proof.
    intros LEN Hfin INIT VALID1 H.
    apply (wp_strong_adequacy_multiple_with_trace_inv heap_lang M Σ s); try done.

    iIntros (?) "".

    iMod (gen_heap_init (heap σ1)) as (genheap)" [Hgen [Hσ _]]".  
    iMod (em_initialization _ s1 (es, σ1) p) as (fGS) "[LM_INIT MSI]"; [done| ].
    Unshelve. 2: by apply hPre. 

    set (distG := {| heap_fairnessGS := (fGS: (em_GS Σ (ExecutionModel := EM))) |}).
    iPoseProof (H distG) as "Hwp". clear H.
    
    iExists state_interp, (λ _ _, ⌜ True ⌝%I), _, (fun τ _ => em_thread_post τ).
    iSplitR.
    { unfold config_wp. iIntros "!>!>" (???????) "?". done. }

    iSpecialize ("Hwp" with "[Hσ LM_INIT]"); [by iFrame| ]. 
    iDestruct "Hwp" as ">[Hwp H]". 
    iModIntro. iFrame "Hwp Hgen MSI".

    iIntros (??????????) "SI POSTS".
    rewrite /rel_always_holds. iDestruct ("H" with "[][][][][][][] SI POSTS") as "R".
    all: try by done.
    iSplit. 
    - iModIntro; iIntros "[$ ?]"; done.
    - eauto. 
  Qed.

  Theorem strong_simulation_adequacy_general
    `{hPre: @heapGpreS Σ M EM} (s: stuckness) (e1 : expr) σ1 (s1: M)
    (R: execution_trace heap_lang → auxiliary_trace M → Prop)
    (p: em_init_param)
    :
    rel_finitary R →
    em_is_init_st ([e1], σ1) s1 ->
    em_valid_state_evolution_fairness {tr[ ([e1], σ1) ]} {tr[ s1 ]} ->
    (wp_premise Σ s e1 σ1 s1 R p) ->
    continued_simulation R (trace_singleton ([e1], σ1)) (trace_singleton s1).
  Proof.
    intros. eapply strong_simulation_adequacy_general_multiple.
    1-4: by eauto.
    apply wp_premise_single. eauto. 
  Qed.

  Theorem strong_simulation_adequacy_inftraces_multiple Σ
    `{hPre: @heapGpreS Σ M EM} (s: stuckness) 
    (es : list expr) σ1 (s1: M)
    (R: execution_trace heap_lang → auxiliary_trace M → Prop)
    (p: em_init_param)
    (iex : inf_execution_trace heap_lang)
    (Hvex : valid_inf_exec (trace_singleton (es, σ1)) iex)
    :
    length es ≥ 1 ->
    rel_finitary R →
    em_is_init_st (es, σ1) s1 ->
    (wp_premise_multiple Σ s es σ1 s1 R p) ->
    exists iatr,
      @valid_inf_system_trace _ M
        (@continued_simulation
           heap_lang
           M
           R)
        (trace_singleton (es, σ1))
        (trace_singleton s1)
        iex
        iatr.
  Proof.
    intros LEN Hfin Hwp.
    eexists.
    eapply produced_inf_aux_trace_valid_inf.
    Unshelve.
    - econstructor.
    - eapply (strong_simulation_adequacy_general_multiple s) => //.
    - done.
  Qed.

  Theorem strong_simulation_adequacy_inftraces Σ
    `{hPre: @heapGpreS Σ M EM} (s: stuckness) 
    (e1 : expr) σ1 (s1: M)
    (R: execution_trace heap_lang → auxiliary_trace M → Prop)
    (p: em_init_param)
    (iex : inf_execution_trace heap_lang)
    (Hvex : valid_inf_exec (trace_singleton ([e1], σ1)) iex)
    :
    rel_finitary R →
    em_is_init_st ([e1], σ1) s1 ->
    (wp_premise Σ s e1 σ1 s1 R p) ->
    exists iatr,
      @valid_inf_system_trace _ M
        (@continued_simulation
           heap_lang
           M
           R)
        (trace_singleton ([e1], σ1))
        (trace_singleton s1)
        iex
        iatr.
  Proof.
    intros. eapply strong_simulation_adequacy_inftraces_multiple.
    1-5: by eauto.
    by eapply wp_premise_single. 
  Qed.

  Theorem strong_simulation_adequacy_traces_multiple Σ
    `{hPre: @heapGpreS Σ M EM} (s: stuckness) 
    (es: list expr) σ1 (s1: M)
    (R: execution_trace heap_lang → auxiliary_trace M → Prop)
    (p: em_init_param)

    (extr : heap_lang_extrace)
    (Hvex : extrace_valid extr)
    (Hexfirst : trfirst extr = (es, σ1))

    (valid_step: cfg heap_lang -> olocale heap_lang → cfg heap_lang → 
                 mstate M → mlabel M → mstate M -> Prop)
    (state_rel: cfg heap_lang -> mstate M -> Prop)
    (lbl_rel: olocale heap_lang -> mlabel M -> Prop)
    (STEP_LBL_REL: forall c1 oζ c2 δ1 ℓ δ2,
                 valid_step c1 oζ c2 δ1 ℓ δ2 ->
                 lbl_rel oζ ℓ)
    (STEP_MTRANS: forall c1 oζ c2 δ1 ℓ δ2,
                 valid_step c1 oζ c2 δ1 ℓ δ2 ->
                 mtrans δ1 ℓ δ2)
    (R_ST: forall extr mtr, R extr mtr -> state_rel (trace_last extr) (trace_last mtr))
    (R_STEP: forall extr mtr, R extr mtr -> valid_state_evolution_fairness valid_step extr mtr)

    :
    length es ≥ 1 ->
    rel_finitary R →
    em_is_init_st (es, σ1) s1 ->
    (wp_premise_multiple Σ s es σ1 s1 R p) ->
    ∃ (mtr : trace (mstate M) (mlabel M)), 
      traces_match lbl_rel state_rel locale_step (@mtrans M) extr mtr /\
      trfirst mtr = s1. 
  Proof.
    intros ? Hfin INIT Hwp.
    have [iatr MATCH] : exists iatr,
        @valid_inf_system_trace
          heap_lang M
          (@continued_simulation
             heap_lang
             M
             R)
          (trace_singleton (es, (trfirst extr).2))
          (trace_singleton s1)
          (from_trace extr)
          iatr.
    { eapply (strong_simulation_adequacy_inftraces_multiple _ s); eauto.
      1: eapply from_trace_preserves_validity; eauto; first econstructor.
      all: try by rewrite Hexfirst. }
    rewrite Hexfirst in MATCH. simpl in *. 
    exists (to_trace s1 iatr).

    split.
    2: { by rewrite to_trace_trfirst. }

    pose proof MATCH as INF_REF. (** see remark below *)
    eapply (valid_inf_system_trace_implies_traces_match
                       valid_step                       
                       state_rel
                       lbl_rel
                       ltac:(idtac)
                       ltac:(idtac)
                       (continued_simulation R)) in MATCH; cycle 1.  
    { intros ?? ?%continued_simulation_rel. eauto. }
    { intros ?? ?%continued_simulation_rel. eauto. }
    { apply from_trace_spec. simpl.
      rewrite Hexfirst. done. }
    { apply to_trace_spec. }
    Unshelve. 2,3: by eauto.
    
    assert (exists len, trace_len.trace_len_is extr len /\ trace_len.trace_len_is (to_trace s1 iatr) len) as LEN. (** see remark below *)
    { simpl in MATCH.
      pose proof (trace_len.trace_has_len extr) as [len LEN]. 
      pose proof (trace_len.trace_has_len (to_trace s1 iatr)) as [len' LEN'].
      eapply trace_len.traces_match_same_length in MATCH; eauto. subst.  
      eauto. }

    (** INF_REF and LEN together give the traces mentioned in
        the refinement section of Lawyer paper
        (same length, related by infinite extension of refinement).       
        However, our proofs proceed differency, 
        using the notion of traces_match (MATCH hypothesis). *)

    apply MATCH. 
  Qed.

  Theorem strong_simulation_adequacy_traces Σ
    `{hPre: @heapGpreS Σ M EM} (s: stuckness) 
    (e1 : expr) σ1 (s1: M)
    (R: execution_trace heap_lang → auxiliary_trace M → Prop)
    (p: em_init_param)

    (extr : heap_lang_extrace)
    (Hvex : extrace_valid extr)
    (Hexfirst : trfirst extr = ([e1], σ1))

    (valid_step: cfg heap_lang -> olocale heap_lang → cfg heap_lang → 
                 mstate M → mlabel M → mstate M -> Prop)
    (state_rel: cfg heap_lang -> mstate M -> Prop)
    (lbl_rel: olocale heap_lang -> mlabel M -> Prop)
    (STEP_LBL_REL: forall c1 oζ c2 δ1 ℓ δ2,
                 valid_step c1 oζ c2 δ1 ℓ δ2 ->
                 lbl_rel oζ ℓ)
    (STEP_MTRANS: forall c1 oζ c2 δ1 ℓ δ2,
                 valid_step c1 oζ c2 δ1 ℓ δ2 ->
                 mtrans δ1 ℓ δ2)
    (R_ST: forall extr mtr, R extr mtr -> state_rel (trace_last extr) (trace_last mtr))
    (R_STEP: forall extr mtr, R extr mtr -> valid_state_evolution_fairness valid_step extr mtr)

    :
    rel_finitary R →
    em_is_init_st ([e1], σ1) s1 ->
    (wp_premise Σ s e1 σ1 s1 R p) ->
    ∃ (mtr : trace (mstate M) (mlabel M)), 
      traces_match lbl_rel state_rel locale_step (@mtrans M) extr mtr /\
      trfirst mtr = s1. 
  Proof.
    intros. eapply strong_simulation_adequacy_traces_multiple; last first.
    { by eapply wp_premise_single. }
    all: by eauto.     
  Qed.
  
End adequacy.
