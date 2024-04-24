From trillium.fairness Require Export fairness resources fuel. 
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import execution_model lm_fair.
From trillium.fairness.lm_rules Require Import resources_updates.


Section LMSteps.

(*   Context `{Countable G}.  *)
(*   Context `{iLM: LiveModel G iM LSI}. *)
(*   Context `{EM: ExecutionModel Λ M}. *)
(*   Context `{eGS: em_GS Σ}.  *)
(*   Context `{invGS_gen HasNoLc Σ}. *)
(*   Context `{Countable (locale Λ)}.  *)
(*   Context {fGS: @fairnessGS _ _ _ _ _ iLM Σ}.  *)

(*   Definition LM_fork_update ζ g  *)
(*     (R1 R2: gset (fmrole iM)) tp1 tp2 *)
(*        (fs: gmap (fmrole iM) nat) *)
(*         (extr : execution_trace Λ) *)
(*         (auxtr: auxiliary_trace M) efork σ1 σ2 *)
(*         Einvs *)
(*           `(R1 ## R2) *)
(*           (* `(fs ≠ ∅) *) *)
(*           `(R2 ≠ ∅) *)
(*           `(R1 ∪ R2 = dom fs) *)
(*           `(fuel_reorder_preserves_LSI (LSI := LSI)) *)
(*          `(trace_last extr = (tp1, σ1)) *)
(*           `(locale_step (tp1, σ1) (Some ζ) (tp2, σ2)) *)
(*           `((∃ tp1', tp2 = tp1' ++ [efork] ∧ length tp1' = length tp1)): iProp Σ := *)
(*      (* ζ ⤞ g -∗ *) *)
(*      has_fuels g (S <$> fs) -∗ *)
(*      em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := eGS) *)
(*      (* ==∗ *) *)
(*      ={Einvs}=∗ *)
(*      ∃ δ2 ℓ g', *)
(*        let ζ' := locale_of tp1 efork in *)
(*          (* ζ' ⤞ g' ∗ *) *)
(*          has_fuels g' (fs ⇂ R2) ∗ *)
(*          (* ζ ⤞ g ∗ *) *)
(*          has_fuels g (fs ⇂ R1) ∗ *)
(*          (partial_mapping_is {[ g' := ∅ ]} -∗ *)
(*             em_thread_post ζ' (em_GS0 := eGS)) ∗ *)
(*          em_msi (tp2, σ2) δ2 (em_GS0 := eGS) ∧  *)
(*          ⌜em_valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[ℓ]: δ2)⌝. *)

  Context `{Countable (locale Λ)}. 
  Context `{iLM: LiveModel (locale Λ) iM LSI}.
  Context {LFP: LMFairPre iLM}.

  Let M__glob := fair_model_model (LM_Fair). 
  Context `{EM: ExecutionModel Λ M__glob}.
  Context `{eGS: em_GS Σ}. 
  Context `{invGS_gen HasNoLc Σ}.
  Context {fGS: @fairnessGS _ _ _ _ _ iLM Σ}. 

  (* Let update_fork_split_def (R1 R2: gset (fmrole iM)) tp1 tp2 *)
  (*      (fs: gmap (fmrole iM) nat) *)
  (*       (extr : execution_trace Λ) *)
  (*       (auxtr: auxiliary_trace M) ζ efork σ1 σ2 *)
  (*         `(R1 ## R2) *)
  (*         (* `(fs ≠ ∅) *) *)
  (*         `(R2 ≠ ∅) *)
  (*         `(R1 ∪ R2 = dom fs) *)
  (*        `(trace_last extr = (tp1, σ1)) *)
  (*         `(locale_step (tp1, σ1) (Some ζ) (tp2, σ2)) *)
  (*         `((∃ tp1', tp2 = tp1' ++ [efork] ∧ length tp1' = length tp1)): iProp Σ := *)
  (*    has_fuels ζ (S <$> fs) -∗ *)
  (*    em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := eGS) ==∗ *)
  (*    ∃ δ2 ℓ, has_fuels (locale_of tp1 efork) (fs ⇂ R2) ∗ *)
  (*            has_fuels ζ (fs ⇂ R1) ∗ *)
  (*            (partial_mapping_is {[ locale_of tp1 efork := ∅ ]} -∗ *)
  (*             em_thread_post (locale_of tp1 efork) (em_GS0 := eGS)) ∗ *)
  (*            em_msi (tp2, σ2) δ2 (em_GS0 := eGS) ∧  *)
  (*            ⌜em_valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[ℓ]: δ2)⌝. *)

    Definition LM_fork_update ζ g Einvs :=
      forall (R1 R2: gset (fmrole iM)) tp1 tp2
       (fs: gmap (fmrole iM) nat)
        (extr : execution_trace Λ)
        (auxtr: auxiliary_trace M__glob) efork σ1 σ2        
          `(R1 ## R2)
          (* `(fs ≠ ∅) *)
          `(R2 ≠ ∅)
          `(R1 ∪ R2 = dom fs)
          `(fuel_reorder_preserves_LSI (LSI := LSI))
         `(trace_last extr = (tp1, σ1))
          `(locale_step (tp1, σ1) (Some ζ) (tp2, σ2))
          `((∃ tp1', tp2 = tp1' ++ [efork] ∧ length tp1' = length tp1)),
     (* ζ ⤞ g -∗ *)
     has_fuels g (S <$> fs) -∗
     em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := eGS)
     (* ==∗ *)
     ={Einvs}=∗
     ∃ δ2 ℓ g',
       let ζ' := locale_of tp1 efork in
         (* ζ' ⤞ g' ∗ *)
         has_fuels g' (fs ⇂ R2) ∗
         (* ζ ⤞ g ∗ *)
         has_fuels g (fs ⇂ R1) ∗
         (partial_mapping_is {[ g' := ∅ ]} -∗
            em_thread_post ζ' (em_GS0 := eGS)) ∗
         em_msi (tp2, σ2) δ2 (em_GS0 := eGS) ∧ 
         ⌜em_valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[ℓ]: δ2)⌝.

End LMSteps.
