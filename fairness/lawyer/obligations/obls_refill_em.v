From iris.proofmode Require Import tactics.
From stdpp Require Import namespaces.
From iris.algebra Require Import auth gmap gset excl gmultiset big_op mono_nat.
From trillium.fairness Require Import fairness locales_helpers execution_model.
From trillium.fairness.lawyer Require Import sub_action_em action_model.
From trillium.fairness.lawyer.obligations Require Import obligations_model obls_refill_model
  obligations_em
  obligations_am
obligations_resources
.


Section ObligationsRefillEM.
  Context {DegO LevelO: ofe}.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}
    `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}
  .

  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  (* Context {Locale: Type}. *)
  Context {Λ: language}.
  Let Locale := locale Λ.

  Context {LIM_STEPS: nat}.
  Context {OP: ObligationsParams Degree Level Locale LIM_STEPS}.

  Let ORM := ObligationsRefillModel.
  Context `{Inhabited Locale}. 
  Let ORAM := ObligationsRefillAM.

  (* TODO: move? *)
  Definition locale_of_orm_lbl (l: mlabel ORM) :=
    match l with | inl τ | inr τ => τ end. 

  Definition obls_refill_valid_evolution_step
    (σ1: cfg Λ) (oζ: olocale Λ) (σ2: cfg Λ)
    (δ1: mstate ORM) (ℓ: mlabel ORM) (δ2: mstate ORM) :=
      mtrans δ1 ℓ δ2 /\
      oζ = Some (locale_of_orm_lbl ℓ)
  .

  Definition obls_refill_ves_wrapper:
    cfg Λ → olocale Λ → cfg Λ → 
    amSt ORAM → Action * option (amRole ORAM) → amSt ORAM → Prop :=

    fun c1 oτ c2 δ1 (aoτ: Action * option om_refill_lbl) δ2 =>
      let '(a, oρ) := aoτ in
      from_option (fun ρ => 
                     obls_refill_valid_evolution_step c1 oτ c2 δ1 ρ δ2 /\
                     a = (if ρ then obls_act else refill_act)
        ) False oρ. 

  Program Definition ObligationsASEM: ActionSubEM Λ ORAM := {| 
      asem_Σ := obls_Σ;
      asem_valid_evolution_step := obls_refill_ves_wrapper;
      asem_initialization Σ := fun {_: ObligationsPreGS Σ} => obls_resources_init Σ;
    |}.
  Next Obligation.
    apply obls_Σ_pre.
  Qed. 

End ObligationsRefillEM.
