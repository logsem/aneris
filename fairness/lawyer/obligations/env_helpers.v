From trillium.fairness.lawyer Require Import sub_action_em.
From trillium.fairness.lawyer.obligations Require Import obligations_model  obligations_am obligations_em obligations_logic obligations_resources.


(* TODO: move all that and use throughout development *)

Class OP_HL (DegO LvlO: ofe) (LIM_STEPS: nat) := {
    om_hl_DegO_discr :: OfeDiscrete DegO; 
    om_hl_LvlO_discr :: OfeDiscrete LvlO; 
    om_hl_LvlO_equiv :: @LeibnizEquiv (ofe_car LvlO) (ofe_equiv LvlO);
    
    om_hl_OPRE :: ObligationsParamsPre (ofe_car DegO) (ofe_car LvlO) LIM_STEPS;
    
    om_hl_OP := LocaleOP (Locale := locale heap_lang);
    om_hl_Degree := ofe_car DegO;
    om_hl_Level := ofe_car LvlO;
}.
Global Existing Instance om_hl_OPRE.
Global Existing Instance om_hl_OP.
Global Existing Instance om_hl_LvlO_discr.
Global Existing Instance om_hl_DegO_discr.
Global Existing Instance om_hl_LvlO_equiv.

Class OM_HL_Env `(OP: OP_HL DegO LvlO LIM_STEPS)
  `(EM: ExecutionModel heap_lang M) (Σ: gFunctors):= {
    ohe_oGS' : @asem_GS _ _ ObligationsASEM Σ;
    ohe_hGS :: heapGS Σ EM;

    ohe_obls_AMU : @AMU_lift_MU _ _ _ ohe_oGS' _ EM ohe_hGS (↑ nroot);
    ohe_obls_AMU__f : forall τ, @AMU_lift_MU__f _ _ _ τ ohe_oGS' _ EM _ ⊤;
    
    ohe_oGS :: ObligationsGS Σ := ohe_oGS';
}.
Global Existing Instance ohe_oGS.
Global Existing Instance ohe_hGS.
