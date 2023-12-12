From stdpp Require Import option.
From Paco Require Import pacotac.
From trillium.fairness Require Import fairness fair_termination fuel fuel_ext traces_match lm_fairness_preservation lm_fair lm_fair_traces.

Definition auxtrace_fairly_terminating {Λ} {Mdl : FairModel} {LSI}
           `{Countable (locale Λ)} {LM : LiveModel (locale Λ) Mdl LSI}
           {LF: LMFairPre LM}
           (auxtr : lmftrace (LM := LM)) :=
  mtrace_valid auxtr →
  (∀ ρ : fmrole Mdl, fair_by_next_TS ρ auxtr) →
  terminating_trace auxtr.

Definition lm_valid_state_evolution_fairness 
  `{Countable (locale Λ)} `{LM:LiveModel (locale Λ) M LSI}
  {LF: LMFairPre LM}
  := 
  valid_state_evolution_fairness (M := fair_model_model LM_Fair) lm_valid_evolution_step.

Theorem continued_simulation_fair_termination
        `{FairTerminatingModel FM} `{Countable (locale Λ)} `(LM:LiveModel (locale Λ) FM LSI)
        {LF: LMFairPre LM}
        (ξ : execution_trace Λ → auxiliary_trace (fair_model_model LM_Fair) → Prop) a1 r1 extr
        (* (LSI0: let f0 := gset_to_gmap (LM.(lm_fl) a1) (FM.(live_roles) a1) in *)
        (*        let m0 := gset_to_gmap r1 (FM.(live_roles) a1) in *)
        (*        LSI a1 m0 f0) *)
        (LSI0: initial_ls_LSI a1 r1)
  :
  (* TODO: This is required for destruttering - Not sure why *)
  (∀ c c', locale_step (Λ := Λ) c None c' -> False) →
  (* The relation must capture that live tids correspond *)
  (forall (ex: execution_trace Λ) (atr: auxiliary_trace (fair_model_model LM_Fair)),
     ξ ex atr -> live_tids (LM:=LM) (trace_last ex) (trace_last atr)) ->
  (* The relation must capture that the traces evolve fairly *)
  (forall (ex: execution_trace Λ) (atr: auxiliary_trace (fair_model_model LM_Fair)),
     ξ ex atr -> lm_valid_state_evolution_fairness ex atr) →
  continued_simulation
    ξ ({tr[trfirst extr]}) ({tr[initial_ls' a1 r1 LSI0]}) →
  extrace_fairly_terminating extr.
Proof.
  intros Hstep Hlive Hvalid Hsim Hvex.
  destruct (infinite_or_finite extr) as [Hinf|]; [|by intros ?].
  assert (∃ iatr,
             valid_inf_system_trace
               (continued_simulation ξ)
               (trace_singleton (trfirst extr))
               (trace_singleton (initial_ls' a1 r1 LSI0))
               (from_trace extr)
               iatr) as [iatr Hiatr].
  { eexists _. eapply produced_inf_aux_trace_valid_inf. econstructor.
    Unshelve.
    - done.
    - eapply from_trace_preserves_validity; eauto; first econstructor. }
  assert (∃ (auxtr : lmftrace), lm_exaux_traces_match extr auxtr (LM := LM))
    as [auxtr Hmatch].
  { exists (to_trace (initial_ls' a1 r1 LSI0) iatr).
    unshelve eapply (valid_inf_system_trace_implies_traces_match
              (lm_valid_evolution_step (LM := LM))
              live_tids
              _
              ltac:(idtac)
              ltac:(idtac)
              (continued_simulation ξ)
              (M := fair_model_model LM_Fair)
      ); eauto.
    - intros ?????? [MATCH _].
      subst. red. by destruct ℓ. 
    - intros ?????? V; by apply V. 
    - intros ? ? ?%continued_simulation_rel. by apply Hlive.
    - intros ? ? ?%continued_simulation_rel. by apply Hvalid.
    - by apply from_trace_spec.
    - by apply to_trace_spec. }
  intros Hfair.
  assert (mtrace_valid auxtr) as Hstutter.
  { by eapply traces_match_valid2. }
  apply can_destutter_auxtr in Hstutter.
  destruct Hstutter as [mtr Hupto].
  have Hfairaux := ex_fairness_preserved
                     extr auxtr Hinf Hmatch Hfair.
  (* have Hvalaux := traces_match_valid2 extr auxtr _ _ _ Hmatch. *)
  pose proof Hmatch as Hvalaux%traces_match_valid2.
  (* pose proof Hfairaux as X%LM_ALM_afair_by_next.  *)
  assert (∀ ρ, fair_by_next_TS ρ auxtr) as Hfairaux'.
  { eapply LM_ALM_afair_by_next; eauto. }
  pose proof (upto_stutter_fairness auxtr mtr Hupto Hfairaux') as Hfairm.   
  have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.
  eapply traces_match_preserves_termination; [apply Hmatch|].
  eapply upto_stutter_finiteness =>//.
  apply fair_terminating_traces_terminate=>//.
Qed.
