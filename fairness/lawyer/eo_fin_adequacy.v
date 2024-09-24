From iris.algebra Require Import auth gmap gset excl excl_auth.
From trillium.fairness.heap_lang Require Import simulation_adequacy.
From trillium.fairness.lawyer Require Import obligations_model obligations_resources.
From trillium.fairness.lawyer Require Import eo_fin. 


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

  Theorem simple_simulation_adequacy_terminate_ftm Σ 

    `{FairTerminatingModelSimple M}

        `{!heapGpreS Σ (@LM_EM_HL _ _ _ LF)} (s: stuckness)
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

  Theorem eofin_terminates
    (N : nat)
    (HN: N > 1)
    (extr : heap_lang_extrace)
    (Hvex : extrace_valid extr)
    (Hexfirst : (trfirst extr).1 = [start #N]):
    (∀ tid, fair_ex tid extr) -> terminating_trace extr.
  Proof.
    assert (heapGpreS eofinΣ EM) as HPreG.
    { apply _. }
    eapply (simulation_adequacy_terminate_ftm yesnoΣ the_model NotStuck _ (N, true) ∅) =>//.
    - eapply valid_state_evolution_finitary_fairness_simple.
      intros ?. simpl. apply (model_finitary s1).
    - intros ?. iStartProof. iIntros "!> (Hm & HFR & Hf) !>". simpl.
      
      iApply (start_spec _ _ 61 with "[Hm Hf HFR]"); eauto.
      
      + iSplitL "Hm"; eauto. do 2 (destruct N; first lia).
        iFrame. iSplit; last (iPureIntro; lia).
        assert ({[Y := 61%nat; No := 61%nat]} = gset_to_gmap 61 {[No;Y]}) as <-; last done.
        rewrite -leibniz_equiv_iff. intros ρ.
        destruct (gset_to_gmap 61 {[Y; No]} !! ρ) as [f|] eqn:Heq.
        * apply lookup_gset_to_gmap_Some in Heq as [Heq ->].
          destruct (decide (ρ = Y)) as [-> |].
          ** rewrite lookup_insert //. rewrite lookup_gset_to_gmap option_guard_True //. set_solver.
          ** rewrite lookup_insert_ne //. assert (ρ = No) as -> by set_solver.
             rewrite lookup_insert // lookup_gset_to_gmap option_guard_True //. set_solver.
        * apply lookup_gset_to_gmap_None in Heq. destruct ρ; set_solver.
  Qed.  

End EOFinAdequacy.
