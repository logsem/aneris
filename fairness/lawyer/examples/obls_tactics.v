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

Ltac burn_cp_after_BOU :=
  iDestruct (cp_mul_take with "CPS") as "[CPS CP]";
  (iSplitR "CP PH"; [iIntros "PH" | iExists _; by iFrame]) ||
  (iSplitR "CP"; [iIntros "PH" | iExists _; by iFrame])
.
                                                           

Ltac BOU_burn_cp :=
  iApply BOU_intro;
  try iNext;
  burn_cp_after_BOU.

Ltac MU_by_BOU :=
  try iNext;
  match goal with
  | [OB_AMU: AMU_lift_MU _ _ _ _ _ |- envs_entails _ (MU _ _ _) ] =>
      iApply OB_AMU; [(try rewrite nclose_nroot); done| ];
      iApply BOU_AMU
  end.

Ltac MU_by_burn_cp := MU_by_BOU; BOU_burn_cp.

Ltac MU__f_by_BOU R' :=
  try iNext;
  match goal with
  | [OBLS_AMU__f: forall τ, @AMU_lift_MU__f _ _ _ _ _ _ _ _ _ |-
                       envs_entails _ (MU__f _ _ _ _) ] =>
      iApply OBLS_AMU__f; [(try rewrite nclose_nroot); done| ];
      iApply (BOU_AMU__f' _ _ _ _ _ R')
  end.

Ltac pure_step_hl :=
  iApply sswp_MU_wp; [done| ];
  iApply sswp_pure_step; [done| ]; simpl;
  iNext.

Ltac pure_step := pure_step_hl; MU_by_burn_cp.
Ltac pure_step_cases := pure_step || (iApply wp_value; []) || wp_bind (RecV _ _ _ _)%V.
Ltac pure_steps := repeat (pure_step_cases; []).

Ltac split_cps cps_res n :=
  let fmt := constr:(("[" ++ cps_res ++ "' " ++ cps_res ++ "]")%string) in
  iDestruct (cp_mul_split' _ _ n with cps_res) as fmt; [lia| ].

