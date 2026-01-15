From iris.proofmode Require Import tactics.
From trillium.program_logic Require Import weakestpre. 
From heap_lang Require Import heap_lang_defs lang notation.
From lawyer.obligations Require Import obligations_resources env_helpers obligations_model.



(* Definition wait_free_method *)
(*   {M} {EM: ExecutionModel heap_lang M} {Σ} `{OP: OP_HL DegO LvlO LIM} *)
(*   {OHE: OM_HL_Env OP EM Σ} *)
(*   (s: stuckness) *)
(*   (m: val) (d: DegO) (F: val -> nat) *)
(*   : iProp Σ := *)
(*   ∀ τ π q (a: val),  *)
(*     {{{ cp_mul π d (F a) ∗ th_phase_frag τ π q }}} *)
(*       App m a @ s ; τ ; ⊤ *)
(*     {{{ v, RET v; th_phase_frag τ π q }}}.  *)


Definition wait_free_method_gen
  {M} {EM: ExecutionModel heap_lang M} {Σ} `{OP: OP_HL DegO LvlO LIM}
  {OHE: OM_HL_Env OP EM Σ}
  (s: stuckness) (* (f: forks_bit) *)
  (m: val) (d: DegO) (F: val -> nat) (P Q: val -> iProp Σ)
  : iProp Σ :=
  ∀ τ π q (a: val), 
    {{{ cp_mul π d (F a) ∗ th_phase_frag τ π q ∗ P a }}}
      App m a @ τ; CannotFork; s; ⊤
    {{{ v, RET v; th_phase_frag τ π q ∗ Q v }}}. 
