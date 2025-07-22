From iris.proofmode Require Import tactics.
From lawyer Require Import program_logic sub_action_em action_model.
From lawyer.examples Require Import obls_tactics.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_model.
From heap_lang Require Import lang.


Section SimpleExample.

  Definition mk_ref: val :=
    λ: "v",
      let: "l" := ref "v" in
      "l"
  .

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.

  Notation "'Degree'" := (om_hl_Degree).
  Context (d: Degree).

  Existing Instance OHE. 

  Lemma mk_ref_spec τ π q (a: val):
    {{{ cp_mul π d 5 ∗ th_phase_frag τ π q }}}
        mk_ref a @ τ
    {{{ (l: loc), RET #l; l ↦ a ∗ th_phase_frag τ π q }}}.
  Proof using.
    iIntros (Φ) "(CPS & PH) POST". rewrite /mk_ref.
    pure_steps.
    wp_bind (ref _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply wp_alloc. iModIntro. iIntros (l) "L _".
    MU_by_burn_cp.
    pure_steps.
    wp_bind (Rec _ _ _)%E. pure_steps.
    iApply "POST". by iFrame.
  Qed.

End SimpleExample.
