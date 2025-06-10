From stdpp Require Import namespaces. 
From iris.proofmode Require Import tactics.
From fairness Require Import fairness.
From lawyer Require Import action_model.
From lawyer.obligations Require Import obligations_model obligations_am.


Section RefillModel.
  Context `{OP: ObligationsParams Degree Level Locale LIM_STEPS}.

  Let PS := ProgressState.

  Inductive refills_cp: PS -> Locale -> PS -> Degree -> Prop :=
  | rcp_step ps τ δ π__max
      (LOC_PHASE: ps_phases ps !! τ = Some π__max):
    refills_cp ps τ (update_cps (ps_cps ps ⊎ {[+ (π__max, δ) +]}) ps) δ.

  Definition om_refill_lbl := (Locale + Locale)%type. 

  Inductive obls_refill_trans: PS -> om_refill_lbl -> PS -> Prop :=
  | ort_burn ps τ ps' (STEP: om_trans ps τ ps'):
    obls_refill_trans ps (inl τ) ps'
  | ort_refill ps τ ps' δ (REFILL: refills_cp ps τ ps' δ):
    obls_refill_trans ps (inr τ) ps'
  .

  Definition ObligationsRefillModel: Model :=
    {| mtrans := obls_refill_trans |}.

  Definition refill_ns: namespace := nroot .@ "refill".
  Definition refill_act: Action := coPpick (↑ refill_ns). 

  Inductive obls_refill_AM_trans: PS → Action * option om_refill_lbl → PS → Prop :=
  | oram_burn δ1 ρ δ2 (STEP: om_trans δ1 ρ δ2):
    obls_refill_AM_trans δ1 (obls_act, Some (inl ρ)) δ2
  | oram_refill δ1 τ δ2 d (REFILL: refills_cp δ1 τ δ2 d):
    obls_refill_AM_trans δ1 (refill_act, Some (inr τ)) δ2
  .

  Context `{Inhabited Locale}.

  Definition ObligationsRefillAM: ActionModel := {| amTrans := obls_refill_AM_trans |}.

End RefillModel.
