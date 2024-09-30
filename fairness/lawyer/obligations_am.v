From stdpp Require Import namespaces. 
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer Require Import obligations_model action_model.


Section ObligationsAM.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Context `{Countable Locale}.
  Context `{Inhabited Locale}.
  Let OM := ObligationsModel OP.

  Definition obls_ns: namespace := nroot .@ "obligations".
  Definition obls_act: Action := coPpick (↑ obls_ns).

  Inductive obls_AM_trans: ProgressState OP → Action * option Locale → ProgressState OP → Prop :=
  | oam_step δ1 ρ δ2
      (STEP: om_trans OP δ1 ρ δ2):
  obls_AM_trans δ1 (obls_act, Some ρ) δ2. 
  
  Global Instance OM_st_eqdec: EqDecision (ProgressState OP).
  Proof. solve_decision. Qed. 

  Global Instance OM_st_inh: Inhabited (ProgressState OP).
  Proof.
    constructor. exact {|
      ps_cps := ∅;
      ps_sigs := ∅;
      ps_obls := ∅;
      ps_eps := ∅;
      ps_phases := ∅;
      ps_exc_bound := 0;
  |}.
  Qed. 
    
  Definition ObligationsAM: ActionModel := {| amTrans := obls_AM_trans |}.

End ObligationsAM.
