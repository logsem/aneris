From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import locales_helpers comp_utils trace_lookup fairness.
From trillium.fairness.lawyer Require Import sub_action_em action_model.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_em obligations_am obls_fairness_preservation.

Section FiniteBranching.
  Context {DegO LevelO: ofe}.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}
    `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}
  .

  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  (* Context {Locale: Type}. *)
  Context {Λ: language}.
  Context `{Countable (locale Λ)}.
  Let Locale := locale Λ.

  Context {LIM_STEPS: nat}.
  Context (OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Let OM := ObligationsModel OP.

  Context `{Inhabited Locale}. 

  Theorem OM_fin_branch c δ
    (tp': list (language.expr Λ))
    (σ': language.state Λ)
    (oζ: olocale Λ):
  quantifiers.smaller_card
    {'(δ', ℓ) : ProgressState OP * (Action * option Locale) | 
      obls_ves_wrapper OP c oζ (tp', σ') δ ℓ δ' ∧
      om_live_tids OP id locale_enabled (tp', σ') δ'} nat.
  Proof using.

  Admitted.     

End FiniteBranching.
