From trillium.fairness Require Import resources execution_model fairness. 
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.

Section ModelPlug.
  (* Context `{Countable G}.  *)
  (* Context `{iLM: LiveModel G iM LSI}. *)
  Context `{EM: ExecutionModel Λ M__glob}.
  Context `{eGS: em_GS Σ}. 
  Context `{invGS_gen HasNoLc Σ}.

  Context {M: FairModel}.
  Context {msi: fmstate M -> iProp Σ}. 
  (* Context `{Countable (locale Λ)}.  *)
  (* Context {PMPP: @PartialModelPredicatesPre G _ _ Σ iM}. *)

  Context (relies_on: locale Λ -> fmrole M -> iProp Σ).
  Context (ε: coPset).

  (* Definition model_lifted_step (P Q: iProp Σ) *)
  (*   (τ: locale Λ) (extr: execution_trace Λ) (auxtr: auxiliary_trace M__glob) c2 *)

  Definition model_plugged: iProp Σ :=
    ∀ P Q (gl: fmrole M),
       □ ((∀ (δ: fmstate M), P ∗ msi δ ==∗ ∃ δ', Q ∗ msi δ' ∗ ⌜ fmtrans M δ (Some gl) δ' ⌝) →
      (∀ (τ: locale Λ) (extr: execution_trace Λ) (auxtr: auxiliary_trace M__glob) c2,
        relies_on τ gl ∗
        P ∗ 
        em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := eGS) ∗
        ⌜ locale_step (trace_last extr) (Some τ) c2 ⌝ 
        ={ ε }=∗
         ∃ (δ2 : M__glob) (ℓ : mlabel M__glob),
         relies_on τ gl ∗
         Q ∗
         em_msi c2 δ2 (em_GS0 := eGS) ∗
         ⌜em_valid_state_evolution_fairness (extr :tr[ Some τ ]: c2) (auxtr :tr[ ℓ ]: δ2)⌝)).

End ModelPlug.
