From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
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
    (Hexfirst : (trfirst extr).1 = [start #N]):
    (* (∀ tid, fair_ex tid extr) -> terminating_trace extr. *)
    extrace_fairly_terminating' extr. 
  Proof.
    assert (heapGpreS eofinΣ EM) as HPreG.
    { apply _. }

    destruct (trfirst extr) as [tp_ σ1] eqn:EX0. simpl in *. subst tp_.                
    
    assert (mstate (ObligationsModel (EO_OP LIM))) as s1.
    { admit. }
    assert (obls_is_init_st (EO_OP LIM) ([start #N], σ1) s1) as INIT.
    { admit. }
    
    pose proof (simple_om_simulation_adequacy_terminate (EO_OP LIM) eofinΣ NotStuck
                  _ _ _ INIT
                  _ EX0) as FAIR_TERM.
    apply FAIR_TERM.

    red. intros ?. iStartProof. iIntros "[HEAP INIT] !>".
    iSplitL.
    - admit.
    - admit. 

  Admitted. 

End EOFinAdequacy.
