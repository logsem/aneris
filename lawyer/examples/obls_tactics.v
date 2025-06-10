From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fixpoint.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import utils.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From lawyer Require Import sub_action_em.
From lawyer Require Import program_logic.

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
  iApply ohe_obls_AMU; [(try rewrite nclose_nroot); done| ];  
  iApply BOU_AMU
.

Ltac MU_by_burn_cp := MU_by_BOU; BOU_burn_cp.

Ltac MU__f_by_BOU R' :=
  try iNext;
  iApply ohe_obls_AMU__f; [(try rewrite nclose_nroot); done| ];
  iApply (BOU_AMU__f' _ _ _ _ _ R')
.

Ltac pure_step_hl :=
  iApply sswp_MU_wp; [done| ];
  iApply sswp_pure_step; [done| ]; simpl;
  iNext.

Ltac pure_step := pure_step_hl; MU_by_burn_cp.
Ltac pure_step_cases := pure_step || (iApply wp_value; []) || wp_bind (RecV _ _ _ _)%V.
Ltac pure_steps := repeat (pure_step_cases; []).

Ltac split_cps cps_res n :=
  let fmt := constr:(("[" ++ cps_res ++ "' " ++ cps_res ++ "]")%string) in
  iDestruct (cp_mul_split' _ _ n with cps_res) as fmt; [try lia| ].


(* Tactics for solving goals related to SB *)
Ltac try_solve_bounds :=
  (try iPureIntro);
  try (match goal with | |- ?x < ?y => red end);
  match goal with
  | BOUND: ?rfl_fl_sb_fun ?u ≤ ?LIM_STEPS |- ?n <= ?LIM_STEPS =>
      etrans; [| apply BOUND];
      try by (rewrite /rfl_fl_sb_fun; simpl; lia)
  | BOUND: ?N ≤ ?LIM_STEPS |- ?n <= ?LIM_STEPS =>
      etrans; [| apply BOUND];
      try by (try unfold N; simpl; lia)
  end.

Ltac use_list_head :=
  match goal with
  | |- ?n ≤ max_list (cons ?i ?l) =>
      trans i; [| simpl; lia];
      (reflexivity || (rewrite Nat.add_comm; simpl; reflexivity))
  end.

Ltac use_rfl_fl_sb :=
  use_list_head ||
  match goal with | |- ?n ≤ ?F _ => rewrite /F; use_list_head end.
