From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fixpoint.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em.
From trillium.fairness.lawyer Require Import program_logic.

Ltac BMU_burn_cp :=
  iApply BMU_intro;
  (* TODO: make a separate tactic *)
  iDestruct (cp_mul_take with "CPS") as "[CPS CP]";
  iSplitR "CP";
  [| do 2 iExists _; iFrame; iPureIntro; done].

Ltac MU_by_BMU :=
  match goal with
  | [OB_AMU: AMU_lift_MU _ _ _ _ _ |- envs_entails _ ?P ] =>
      iApply OB_AMU; [by rewrite nclose_nroot| ];
      iApply (BMU_AMU with "[-PH] [$]"); [by eauto| ]; iIntros "PH"
  end.

Ltac MU_by_burn_cp := MU_by_BMU; BMU_burn_cp.

Ltac pure_step_hl :=
  iApply sswp_MU_wp; [done| ];
  iApply sswp_pure_step; [done| ]; simpl;
  iNext.

Ltac pure_step := pure_step_hl; MU_by_burn_cp.
Ltac pure_step_cases := pure_step || (iApply wp_value; []) || wp_bind (RecV _ _ _ _)%V.
Ltac pure_steps := repeat (pure_step_cases; []).

(* TODO: move, remove duplicates *)
Ltac split_cps cps_res n :=
  let fmt := constr:(("[" ++ cps_res ++ "' " ++ cps_res ++ "]")%string) in
  iDestruct (cp_mul_split' _ _ n with cps_res) as fmt; [lia| ].

