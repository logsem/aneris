From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import execution_model.
From trillium.fairness Require Import fairness fuel resources. 
From trillium.fairness.lm_rules Require Import resources_updates. 


Section PartialModelPredicates.
  (* Context `{Countable G}.  *)
  Context `{Countable (locale Λ)}. 
  Context `{iLM: LiveModel (locale Λ) iM LSI_True}.
  Context `{EM: ExecutionModel Λ M}.
  Context `{eGS: em_GS Σ}. 
  Context `{invGS_gen HasNoLc Σ}.
  Context {fGS: @fairnessGS _ _ _ _ _ iLM Σ}. 
  (* Context {PMPP: @PartialModelPredicatesPre (locale Λ) _ _ Σ iM}. *)

  Let update_no_step_enough_fuel_def (extr : execution_trace Λ) 
      (auxtr : auxiliary_trace M) 
      (c2 : cfg Λ) (fs : gmap (fmrole iM) nat) (ζ : locale Λ)
      `(dom fs ≠ ∅)
      `(locale_step (trace_last extr) (Some ζ) c2): iProp Σ :=
    has_fuels ζ (S <$> fs) -∗
    em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := eGS) ==∗
    ∃ (δ2 : M) (ℓ : mlabel M),
      ⌜em_valid_state_evolution_fairness (extr :tr[ Some ζ ]: c2)
      (auxtr :tr[ ℓ ]: δ2)⌝ ∗
      has_fuels ζ (filter (λ '(k, _), k ∈ dom fs ∖ ∅) fs) ∗
      em_msi c2 δ2 (em_GS0 := eGS).
  
  Let update_fork_split_def (R1 R2: gset (fmrole iM)) tp1 tp2
       (fs: gmap (fmrole iM) nat)
        (extr : execution_trace Λ)
        (auxtr: auxiliary_trace M) ζ efork σ1 σ2
          `(R1 ## R2)
          (* `(fs ≠ ∅) *)
          `(R2 ≠ ∅)
          `(R1 ∪ R2 = dom fs)
         `(trace_last extr = (tp1, σ1))
          `(locale_step (tp1, σ1) (Some ζ) (tp2, σ2))
          `((∃ tp1', tp2 = tp1' ++ [efork] ∧ length tp1' = length tp1)): iProp Σ :=
     has_fuels ζ (S <$> fs) -∗
     em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := eGS) ==∗
     ∃ δ2 ℓ, has_fuels (locale_of tp1 efork) (fs ⇂ R2) ∗
             has_fuels ζ (fs ⇂ R1) ∗
             (partial_mapping_is {[ locale_of tp1 efork := ∅ ]} -∗
              em_thread_post (locale_of tp1 efork) (em_GS0 := eGS)) ∗
             em_msi (tp2, σ2) δ2 (em_GS0 := eGS) ∧ 
             ⌜em_valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[ℓ]: δ2)⌝.
 
    Let update_step_still_alive_def
      (extr : execution_trace Λ)
      (auxtr: auxiliary_trace M)
       tp1 tp2 σ1 σ2
       (s1 s2: iM)
       (fs1 fs2: gmap (fmrole iM) nat)
      ρ (δ1 : M) ζ fr1 fr_stash
       (Einvs: coPset)
     `((live_roles _ s2 ∖ live_roles _ s1) ⊆ fr1 ∪ dom fs1 ∩ dom fs2)
     `(fr_stash ⊆ dom fs1)
     `((live_roles _ s1) ∩ (fr_stash ∖ {[ ρ ]}) = ∅)
     `(dom fs2 ∩ fr_stash = ∅)
    `(trace_last extr = (tp1, σ1))
    `(trace_last auxtr = δ1)
     `(locale_step (tp1, σ1) (Some ζ) (tp2, σ2))
     `(fmtrans _ s1 (Some ρ) s2)
      `(valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := iLM)): iProp Σ :=
      has_fuels ζ fs1 -∗
      partial_model_is s1 -∗
      em_msi (tp1, σ1) δ1 (em_GS0 := eGS) -∗
      partial_free_roles_are fr1
      ={ Einvs }=∗
      ∃ (δ2: M) ℓ,
      ⌜em_valid_state_evolution_fairness (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[ℓ]: δ2)⌝ ∗
      has_fuels ζ fs2 ∗
      partial_model_is s2 ∗
      em_msi (tp2, σ2) δ2 (em_GS0 := eGS)∗
      partial_free_roles_are (fr1 ∖ (live_roles _ s2 ∖ (live_roles _ s1 ∪ dom fs1 ∩ dom fs2)) ∪ fr_stash).

    (* TODO: where to place it? *)
    (* Let partial_free_roles_fuels_disj_def δ fr fs tid: iProp Σ := *)
    (*     partial_msi δ -∗ partial_free_roles_are fr -∗ has_fuels tid fs -∗ ⌜ fr ## dom fs ⌝. *)

    Let PMP_def (Einvs: coPset): iProp Σ := □ (
          (∀ extr auxtr c2 fs ζ NE STEP, update_no_step_enough_fuel_def extr auxtr c2 fs ζ NE STEP) ∗
          (∀ R1 R2 tp1 tp2 fs extr auxtr ζ efork σ1 σ2 DISJ NE DOM LAST STEP POOL, update_fork_split_def R1 R2 tp1 tp2 fs extr auxtr ζ efork σ1 σ2 DISJ NE DOM LAST STEP POOL) ∗
          (∀ extr auxtr tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ δ1 ζ fr1 fr_stash
             LR STASH STASH' STASH'' LAST1 LAST2 STEP STEP' VFM,
              @update_step_still_alive_def extr auxtr tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ δ1 ζ fr1 fr_stash Einvs LR STASH STASH' STASH'' LAST1 LAST2 STEP STEP' VFM)
).  

    Definition PartialModelPredicates Einvs: iProp Σ := PMP_def Einvs. 

    Lemma Build_PartialModelPredicates Einvs:
      PMP_def Einvs ⊢ PartialModelPredicates Einvs.
    Proof. done. Qed. 

    Global Instance PMP_pers: forall Einvs, Persistent (PartialModelPredicates Einvs). 
    Proof. apply _. Qed.

    Lemma update_no_step_enough_fuel {Einvs} extr auxtr c2 fs ζ NE STEP: 
      PartialModelPredicates Einvs ⊢ update_no_step_enough_fuel_def extr auxtr c2 fs ζ NE STEP. 
    Proof. by iIntros "(?&?&?)". Qed.
    Lemma update_fork_split {Einvs} R1 R2 tp1 tp2 fs extr auxtr ζ efork σ1 σ2 DISJ NE DOM LAST STEP POOL: 
      PartialModelPredicates Einvs ⊢ update_fork_split_def R1 R2 tp1 tp2 fs extr auxtr ζ efork σ1 σ2 DISJ NE DOM LAST STEP POOL. 
    Proof. by iIntros "(?&?&?)". Qed.
    Lemma update_step_still_alive {Einvs} extr auxtr tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ δ1 ζ fr1 fr_stash LR STASH STASH' STASH'' LAST1 LAST2 STEP STEP' VFM:
      PartialModelPredicates Einvs ⊢ update_step_still_alive_def extr auxtr tp1 tp2 σ1 σ2 s1 s2 fs1 fs2 ρ δ1 ζ fr1 fr_stash Einvs LR STASH STASH' STASH'' LAST1 LAST2 STEP STEP' VFM.
    Proof. by iIntros "(?&?&?)". Qed. 

    Global Opaque PartialModelPredicates.

End PartialModelPredicates.
