From iris.algebra Require Import auth gmap gset excl excl_auth.
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

  (* Definition live_rel (ex : execution_trace Λ) (aux : auxiliary_trace (fair_model_model LM_Fair)) := *)
  (* live_tids (LM:=LM) (trace_last ex) (trace_last aux). *)

  (* Definition sim_rel (ex : execution_trace Λ) (aux : auxiliary_trace (fair_model_model LM_Fair)) := *)
  (*   valid_state_evolution_fairness lm_valid_evolution_step ex aux (M := (fair_model_model LM_Fair)) ∧ live_rel ex aux. *)

  (* Definition sim_rel_with_user (ξ : execution_trace Λ -> finite_trace M (option (fmrole M)) -> Prop) *)
  (* (ex : execution_trace Λ) (aux : auxiliary_trace (fair_model_model LM_Fair)) := *)
  (* sim_rel ex aux ∧ ξ ex (get_underlying_fairness_trace aux). *)

  Definition exec_om_rel (ex : execution_trace heap_lang) (aux : auxiliary_trace OM): Prop.
  Admitted. 


  Theorem om_simulation_adequacy_model_trace Σ
    (* `{FairTerminatingModelSimple M} *)
        `{!heapGpreS Σ EM} (s: stuckness)
        (e1: expr) (s1: mstate OM) (* p *)
        (* (LSI0: initial_ls_LSI s1 0) *)
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])    :
    (* rel_finitary (sim_rel LM) → *)
    wp_premise Σ s e1 (trfirst extr).2 s1 exec_om_rel (tt: @em_init_param _ _ EM) ->
    (* The coinductive pure coq proposition given by adequacy *)
    ∃ (auxtr : obls_trace), 
      lm_exaux_traces_match extr auxtr (LM := LM) ∧
      trfirst auxtr = s1.
  Proof.
    intros Hfb Hwp.
    destruct (simulation_adequacy_traces
                Σ _ e1 s1 _ LSI0 extr Hvex Hexfirst Hfb Hwp) as (auxtr & Hmatch & A0).
    assert (mtrace_valid auxtr) as Hstutter.
    { by eapply traces_match_valid2 in Hmatch. }
    destruct (can_destutter_auxtr auxtr) as [mtr Hupto] =>//.
    eauto.
  Qed.

  Theorem simple_om_simulation_adequacy_terminate Σ 
    (* `{FairTerminatingModelSimple M} *)
        `{!heapGpreS Σ EM} (s: stuckness)
        (e1: expr) (s1: mstate OM) (* p *)
        (* (LSI0: initial_ls_LSI s1 0) *)
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])
    :
    (* rel_finitary (sim_rel LM) → *)
    wp_premise Σ s e1 (trfirst extr).2 s1 exec_om_rel (tt: @em_init_param _ _ EM) -> 
    extrace_fairly_terminating' extr.
  Proof.
    intros (* Hterm Hfb *) Hwp Hvex Hfair.
    
    destruct (simulation_adequacy_model_trace
                Σ _ e1 s1 _ LSI0 extr Hvex Hexfirst Hfb Hwp) as (auxtr&mtr&Hmatch&Hupto&A0).
    have Hfairaux := ex_fairness_preserved 
                       extr auxtr Hmatch Hfair.
    pose proof (proj1 (LM_ALM_afair_by_next LM auxtr) (Hfairaux LF)) as Hfairaux'. 
    have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux'.
    pose proof Hmatch as Hvalaux%traces_match_valid2. 
    have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.
    pose proof Hupto as M0%upto_stutter_trfirst. rewrite A0 in M0.  
    have Htermtr := Hterm mtr M0 Hmtrvalid Hfairm.
    eapply traces_match_preserves_termination =>//.
    eapply upto_stutter_finiteness =>//.
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
