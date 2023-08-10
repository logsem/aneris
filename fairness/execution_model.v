From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From trillium Require Import language.
From trillium.program_logic Require Import traces weakestpre.
From trillium.fairness Require Import inftraces fairness. 

Class ExecutionModel (Λ: language) (M: Model) := {

    (* TODO: how to express that these two are typeclasses themselves? *)
    em_preGS: gFunctors -> Set;
    em_GS: gFunctors -> Set;
    em_Σ: gFunctors;
    em_Σ_subG: forall Σ, subG em_Σ Σ -> em_preGS Σ;

    em_valid_evolution_step:
    olocale Λ → cfg Λ → mstate M → mlabel M → mstate M → Prop;

    (* em_fork_post {Σ} *)
    em_thread_post {Σ} `{em_GS Σ}
    : locale Λ ->
      (* val -> *)
      iProp Σ;
    em_msi {Σ} `{em_GS Σ}: cfg Λ -> mstate M -> iProp Σ;
    
    em_init_resource {Σ: gFunctors} `{em_GS Σ}: mstate M → iProp Σ;
    (* TODO: currently we assume that postconditions of all threads coincide *)
    (* em_init_thread_post {Σ}: locale Λ -> val -> iProp Σ; *)
    em_is_init_st: cfg Λ -> mstate M -> Prop;
    
    em_initialization Σ `{ePreGS: em_preGS Σ}: 
    forall (s1: mstate M) (σ: cfg Λ)
      (INIT_ST: em_is_init_st σ s1),
      ⊢ (|==> ∃ eGS: em_GS Σ, @em_init_resource _ eGS s1 ∗ @em_msi _ eGS σ s1)
}.

Section EMDefinitions.
  Context `{EM: ExecutionModel Λ M}. 

  Definition em_valid_state_evolution_fairness
    (extr : execution_trace Λ) (auxtr: auxiliary_trace M) :=
    match extr, auxtr with
    | (extr :tr[oζ]: σ), auxtr :tr[ℓ]: δ =>
        (* labels_match (LM:=LM) oζ ℓ ∧ LM.(lm_ls_trans) (trace_last auxtr) ℓ δ ∧ *)
        (* tids_smaller es δ *)
      em_valid_evolution_step oζ σ (trace_last auxtr) ℓ δ
    | _, _ => True
    end.

  (* TODO: where is that needed? *)
  Definition valid_lift_fairness
    (φ: execution_trace Λ -> auxiliary_trace M -> Prop)
    (extr : execution_trace Λ) (auxtr : auxiliary_trace M) :=
    em_valid_state_evolution_fairness extr auxtr ∧ φ extr auxtr.

End EMDefinitions.

