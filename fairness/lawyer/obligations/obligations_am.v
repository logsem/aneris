From stdpp Require Import namespaces. 
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer.obligations Require Import obligations_model.
From trillium.fairness.lawyer Require Import action_model.


Section ObligationsAM.
  Context `{OP: ObligationsParams Degree Level Locale LIM_STEPS}.
  Context {INH_LOC: Inhabited Locale}.
  Let OM := ObligationsModel.

  Definition obls_ns: namespace := nroot .@ "obligations".
  Definition obls_act: Action := coPpick (↑ obls_ns).

  Inductive obls_AM_trans: ProgressState → Action * option Locale → ProgressState → Prop :=
  | oam_step δ1 ρ δ2
      (STEP: om_trans δ1 ρ δ2):
  obls_AM_trans δ1 (obls_act, Some ρ) δ2. 
  
  Global Instance OM_st_eqdec: EqDecision ProgressState.
  Proof. solve_decision. Qed. 

  Global Instance OM_st_inh: Inhabited ProgressState.
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

  (* Global Instance is_act_of_obls_dec: forall a, Decision (is_action_of ObligationsAM a). *)
  (* Proof using. *)
  (*   intros. destruct (decide (a = obls_act)) as [-> | ?]. *)
  (*   { left. red. *)
  (*     destruct OM_st_inh as [δ], INH_LOC as [τ].  *)

End ObligationsAM.
