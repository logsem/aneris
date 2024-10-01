From stdpp Require Import namespaces. 
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness.
From trillium.fairness.lawyer Require Import action_model.


Definition cnt_st := nat. 
Definition cnt_lbl := unit. 
Inductive cnt_trans: cnt_st -> cnt_lbl -> cnt_st -> Prop :=
  | cnt_trans_incr n: cnt_trans n tt (S n)
.

Definition CounterModel: Model := {| mtrans := cnt_trans |}. 

(* TODO: add a parameter when we'll use multiple CMs *)
Definition cnt_ns: namespace := nroot .@ "counter".
Definition cnt_act: Action := coPpick (↑ cnt_ns).

Inductive cnt_AM_trans: cnt_st → Action * option cnt_lbl → cnt_st → Prop :=
  | cnt_am_step δ1 ρ δ2 (STEP: cnt_trans δ1 ρ δ2):
    cnt_AM_trans δ1 (cnt_act, Some ρ) δ2. 
  
Definition CounterAM: ActionModel := {| amTrans := cnt_AM_trans |}.
