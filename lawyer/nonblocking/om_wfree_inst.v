From iris.proofmode Require Import tactics.
From lawyer.examples Require Import orders_lib.
From lawyer.obligations Require Import env_helpers obligations_model.
From lawyer.nonblocking.logrel Require Import logrel.


Definition WF_Degree := bounded_nat 2.
Definition WF_Level := unit.
Definition WF_SB := 2.

Instance OPP_WF: ObligationsParamsPre WF_Degree WF_Level WF_SB.
esplit; try by apply _.
- apply nat_bounded_PO.
- apply unit_PO.
Defined.


Instance OP_HL_WF: OP_HL WF_Degree WF_Level WF_SB := {| om_hl_OPRE := OPP_WF |}.


Definition d_wfr0: WF_Degree. refine (ith_bn 2 0 _). abstract lia. Defined.
Definition d_wfr1: WF_Degree. refine (ith_bn 2 1 _). abstract lia. Defined.
Definition l_wfr: WF_Level := tt.


Declare Scope WFR_scope.

Notation "'d0'" := (d_wfr0) : WFR_scope.
Notation "'d1'" := (d_wfr1) : WFR_scope.
Notation "'l0'" := (l_wfr) : WFR_scope.

Notation "'Degree'" := (WF_Degree) : WFR_scope.
Notation "'Level'" := (WF_Level) : WFR_scope.



From trillium.program_logic Require Import weakestpre. 
From heap_lang Require Import heap_lang_defs lang notation.
From lawyer.obligations Require Import obligations_resources.


(* TODO: relax to non-trivial degrees *)
(* TODO: support LATs *)
Record WaitFreeSpec (m: val) := {
  wfs_is_init_st: cfg heap_lang -> Prop;
  wfs_mod_inv {M: Model} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ}: iProp Σ;
  wfs_mod_inv_Pers `{EM: ExecutionModel heap_lang M} `{OHE: !OM_HL_Env OP_HL_WF EM Σ} ::
    Persistent wfs_mod_inv;
  wfs_init_mod `{EM: ExecutionModel heap_lang M} `{OHE: !OM_HL_Env OP_HL_WF EM Σ}:
    forall c (INIT: wfs_is_init_st c),
      let _: heap1GS Σ := iem_phys _ EM in 
      ⊢ hl_phys_init_resource c ={⊤}=∗ wfs_mod_inv;
  wfs_F: nat;
  wfs_spec:
  forall {M: Model} {EM: ExecutionModel heap_lang M} Σ {OHE: OM_HL_Env OP_HL_WF EM Σ}
    τ π q (a: val),
    {{{ cp_mul π d_wfr0 wfs_F ∗ th_phase_frag τ π q ∗ wfs_mod_inv}}}
      App m a @ τ
    {{{ v, RET v; th_phase_frag τ π q }}};

  (* TODO: derive it from wfs_spec *)
  wfs_safety_spec:
    ∀ {Σ : gFunctors} `{heap1GS Σ, invGS_gen HasNoLc Σ},
      ⊢ interp m;
}. 
