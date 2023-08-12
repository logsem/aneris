From stdpp Require Import option.
From Paco Require Import pacotac.
From trillium.fairness Require Export fairness fair_termination fuel traces_match lm_fairness_preservation.

Definition auxtrace_fairly_terminating {Λ} {Mdl : FairModel}
           {LM : LiveModel (locale Λ) Mdl} (auxtr : auxtrace (LM := LM)) :=
  auxtrace_valid (LM:=LM) auxtr →
  (∀ ρ, fair_aux ρ auxtr (LM := LM)) →
  terminating_trace auxtr.

Definition lm_valid_state_evolution_fairness 
  `{LM:LiveModel (locale Λ) M} `{EqDecision (locale Λ)} := 
  valid_state_evolution_fairness (M := LM) lm_valid_evolution_step.

Theorem continued_simulation_fair_termination
        `{FairTerminatingModel FM} `(LM:LiveModel (locale Λ) FM) `{Countable (locale Λ)}
        (ξ : execution_trace Λ → auxiliary_trace LM → Prop) a1 r1 extr :
  (* TODO: This is required for destruttering - Not sure why *)
  (∀ c c', locale_step (Λ := Λ) c None c' -> False) →
  (* The relation must capture that live tids correspond *)
  (forall (ex: execution_trace Λ) (atr: auxiliary_trace LM),
     ξ ex atr -> live_tids (LM:=LM) (trace_last ex) (trace_last atr)) ->
  (* The relation must capture that the traces evolve fairly *)
  (forall (ex: execution_trace Λ) (atr: auxiliary_trace LM),
     ξ ex atr -> lm_valid_state_evolution_fairness ex atr) →
  continued_simulation
    ξ ({tr[trfirst extr]}) ({tr[initial_ls a1 r1]}) →
  extrace_fairly_terminating extr.
Proof.
  intros Hstep Hlive Hvalid Hsim Hvex.
  destruct (infinite_or_finite extr) as [Hinf|]; [|by intros ?].
  assert (∃ iatr,
             valid_inf_system_trace
               (continued_simulation ξ)
               (trace_singleton (trfirst extr))
               (trace_singleton (initial_ls a1 r1))
               (from_trace extr)
               iatr) as [iatr Hiatr].
  { eexists _. eapply produced_inf_aux_trace_valid_inf. econstructor.
    Unshelve.
    - done.
    - eapply from_trace_preserves_validity; eauto; first econstructor. }
  assert (∃ (auxtr : auxtrace (LM := LM)), lm_exaux_traces_match extr auxtr)
    as [auxtr Hmatch].
  { exists (to_trace (initial_ls a1 r1) iatr).
    unshelve eapply (valid_inf_system_trace_implies_traces_match
              (lm_valid_evolution_step (LM := LM))
              live_tids
              labels_match
              ltac:(idtac)
              ltac:(idtac)
              (continued_simulation ξ)); eauto.
    1, 2: intros ?????? V; by apply V. 
    - intros ? ? ?%continued_simulation_rel. by apply Hlive.
    - intros ? ? ?%continued_simulation_rel. by apply Hvalid.
    - by apply from_trace_spec.
    - by apply to_trace_spec. }
  intros Hfair.
  assert (auxtrace_valid auxtr (LM := LM)) as Hstutter.
  { by eapply traces_match_LM_preserves_validity. }
  apply can_destutter_auxtr in Hstutter.
  destruct Hstutter as [mtr Hupto].
  have Hfairaux := fairness_preserved extr auxtr Hinf Hmatch Hfair.
  have Hvalaux := traces_match_LM_preserves_validity extr auxtr _ _ _ Hmatch.
  have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux.
  have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.
  eapply traces_match_preserves_termination; [apply Hmatch|].
  eapply upto_stutter_finiteness =>//.
  apply fair_terminating_traces_terminate=>//.
Qed.
