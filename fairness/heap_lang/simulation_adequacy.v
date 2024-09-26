From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre adequacy.
From trillium.fairness Require Export fairness traces_match.
From trillium.fairness.heap_lang Require Export lang heap_lang_defs.

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
        ⊢ (([∗ map] l ↦ v ∈ heap σ1, mapsto l (DfracOwn 1) v) ∗
             em_init_resource s1 p (em_GS0 := heap_fairnessGS)
           ={⊤}=∗
              WP e1 @ s; locale_of [] e1; ⊤ {{ _, em_thread_post 0%nat (em_GS0 := heap_fairnessGS)}} ∗
                                            rel_always_holds0 R s state_interp (fun _ => em_thread_post 0%nat (em_GS0 := heap_fairnessGS)) e1 σ1 s1)). 


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
    intros Hfin INIT VALID1 H.

    (* apply (wp_strong_adequacy heap_lang M Σ s); first by eauto. *)
    intros. apply (wp_strong_adequacy heap_lang M Σ s); [done| ]. 
    iIntros (?) "".

    iMod (gen_heap_init (heap σ1)) as (genheap)" [Hgen [Hσ _]]".  
    (* iMod (init_fairnessGS_LM _ _ s1 e1) as (fGS) "GEN".    *)
    iMod (em_initialization _ s1 ([e1], σ1) p) as (fGS) "[LM_INIT MSI]"; [done| ].
    Unshelve. 2: by apply hPre. 

    set (distG := {| heap_fairnessGS := (fGS: (em_GS Σ (ExecutionModel := EM))) |}).
    (* iMod (H distG) as "Hwp". clear H. *)
    iPoseProof (H distG) as "Hwp". clear H.
    
    iExists state_interp, (fun _ => em_thread_post 0%nat), fork_post.
    iSplitR.
    { unfold config_wp. iIntros "!>!>" (???????) "?". done. }

    iSpecialize ("Hwp" with "[Hσ LM_INIT]"); [by iFrame| ]. 
    iDestruct "Hwp" as ">[Hwp H]". 
    iModIntro. iFrame.
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
    intros Hfin Hwp.
    eexists.
    eapply produced_inf_aux_trace_valid_inf.
    Unshelve.
    - econstructor.
    - eapply (strong_simulation_adequacy_general s) => //.
    - done.
  Qed.

  Definition FOO {M: Model}: extrace heap_lang -> trace (mstate M) (mlabel M) -> Prop.
  Admitted.

  (* TODO: move *)
  Definition to_trace_trfirst {S L : Type}
    (s: S) (il: inflist (L * S)):
    trfirst (to_trace s il) = s.
  Proof. 
    destruct il as [| [??]]; done.
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
    intros Hfin INIT Hwp.
    have [iatr Hbig] : exists iatr,
        @valid_inf_system_trace
          heap_lang M
          (@continued_simulation
             heap_lang
             M
             R)
          (trace_singleton ([e1], (trfirst extr).2))
          (trace_singleton s1)
          (from_trace extr)
          iatr.
    { eapply (strong_simulation_adequacy_inftraces _ s); eauto.
      eapply from_trace_preserves_validity; eauto; first econstructor.
      all: by rewrite Hexfirst. }
    exists (to_trace s1 iatr).
    split.
    2: { by rewrite to_trace_trfirst. }
    
    unshelve eapply (valid_inf_system_trace_implies_traces_match
                       valid_step                       
                       state_rel
                       lbl_rel
                       ltac:(idtac)
                       ltac:(idtac)
                       (continued_simulation R)); eauto.
    - intros ?? ?%continued_simulation_rel. eauto.
    - intros ?? ?%continued_simulation_rel. eauto.
    - apply from_trace_spec. simpl.
      rewrite Hexfirst. done. 
    - apply to_trace_spec. 
  Qed.
  
End adequacy.
