From iris.proofmode Require Import tactics.
From stdpp Require Import namespaces.
From iris.algebra Require Import auth excl.
From trillium.fairness Require Import fairness locales_helpers execution_model.
From trillium.fairness.lawyer.counter Require Import counter_model counter_resources.


Section CounterEM.
  Context `{Λ: language}.

  Let CM := CounterModel.
      
  Definition cnt_valid_evolution_step
    (σ1: cfg Λ) (oζ: olocale Λ) (σ2: cfg Λ)
    (δ1: mstate CM) (ℓ: mlabel CM) (δ2: mstate CM) :=
      mtrans δ1 ℓ δ2
  .

  Definition cnt_si `{!CounterGS Σ}
    (σ: cfg Λ) (δ: mstate CM): iProp Σ :=
      cnt_msi δ
  . 

  Definition cnt_init_resource `{!CounterGS Σ}
    (n: mstate CM) (_: unit): iProp Σ :=
    frag_cnt_is n
  .

  Definition cnt_is_init_st (_: cfg Λ) (δ: mstate CM) := True. 

  Lemma cnt_resources_init Σ {PRE: CounterPreGS Σ}:
    ∀ s1 σ p (INIT: cnt_is_init_st σ s1),
        ⊢ |==> ∃ eGS: CounterGS Σ, cnt_init_resource s1 p ∗ cnt_si σ s1. 
  Proof using.
    simpl. intros n σ ? INIT. iStartProof.
    iMod (own_alloc (● (Excl' n)  ⋅ ◯ _)) as (?) "[CNTa CNTf]".
    { by apply auth_both_valid_2. }
    iModIntro. iExists {| cnt_pre := PRE; |}.
    iFrame.
  Qed.

  (* Definition ObligationsEM: ExecutionModel Λ OM := *)
  (*   {|  *)
  (*     em_Σ := obls_Σ OP; *)
  (*     em_valid_evolution_step := obls_valid_evolution_step; *)
  (*     em_thread_post Σ `{!ObligationsGS OP Σ} := *)
  (*       fun τ => (obls _ τ ∅)%I; *)
  (*     em_initialization := obls_resources_init; *)
  (*   |}. *)

  Definition init_cnt_state (n: nat): mstate CM := n. 

  Lemma init_cnt_state_init c n:
    cnt_is_init_st c (init_cnt_state n).
  Proof. done. Qed. 
    
  From trillium.fairness.lawyer Require Import sub_action_em obligations_am action_model. 
  (* Context `{Inhabited Locale}.  *)
  Let CAM := CounterAM. 

  Definition cnt_ves_wrapper:
    cfg Λ → olocale Λ → cfg Λ → 
    amSt CAM → Action * option (amRole CAM) → amSt CAM → Prop :=

    fun c1 oτ c2 δ1 (aoτ: Action * option unit) δ2 =>
      let '(a, oρ) := aoτ in
      from_option (fun ρ => cnt_valid_evolution_step c1 oτ c2 δ1 ρ δ2) False oρ /\
      a = cnt_act
  . 

  Definition CounterASEM: ActionSubEM Λ CAM :=
    {| 
      asem_Σ := cnt_Σ;
      asem_valid_evolution_step := cnt_ves_wrapper;
      asem_initialization := cnt_resources_init;
    |}.

End CounterEM.
