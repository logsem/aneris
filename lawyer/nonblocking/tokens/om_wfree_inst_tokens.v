From iris.proofmode Require Import tactics.
From lawyer.examples Require Import orders_lib.
From lawyer.obligations Require Import env_helpers obligations_model.
From lawyer.nonblocking Require Import om_wfree_inst.
From lawyer.nonblocking.logrel Require Import logrel.


From trillium.program_logic Require Import weakestpre. 
From heap_lang Require Import heap_lang_defs lang notation.
From lawyer.obligations Require Import obligations_resources.


Lemma foo:
  forall {M: Model} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ},
    heap1GS Σ.
Proof using.
  intros.
  exact (iem_phys _ EM).
  Show Proof.
  Abort. 

Lemma foo:
  forall {M: Model} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ},
    invGS_gen HasNoLc Σ.
Proof using.
  intros.
  apply _.
  Show Proof. 
Abort. 


(* TODO: generalize the token type *)
From iris.algebra Require Import excl. 
Class UnitTokenPre Σ := {
    ut_pre_tok :: inG Σ (exclR unit);
}.
Class UnitToken Σ := {
    ut_pre_pre :: UnitTokenPre Σ;
    ut_γ: gname;
}.
Definition unit_tok `{UnitToken Σ} := own ut_γ (Excl ()). 

Record WaitFreeSpecToken (m: val) := {
  wfst_is_init_st: cfg heap_lang -> Prop;
  (** for wait-free modules, we expect that invariant doesn't contain OM resources *)
  wfst_mod_inv {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}: iProp Σ;
  wfst_mod_inv_Pers `{heap1GS Σ, invGS_gen HasNoLc Σ} ::
    Persistent wfst_mod_inv;
  wfst_init_mod `{heap1GS Σ, invGS_gen HasNoLc Σ}:
    forall c (INIT: wfst_is_init_st c),
      ⊢ hl_phys_init_resource c ={⊤}=∗ wfst_mod_inv;
  wfst_F: nat;
  wfst_spec:
  forall {M: Model} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ}
    {UT: UnitToken Σ}
    τ π q (a: val),
    {{{ cp_mul π d_wfr0 wfst_F ∗ th_phase_frag τ π q ∗ 
        (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfst_mod_inv ) ∗
        unit_tok
    }}}
      App m a @ τ
    {{{ v, RET v; th_phase_frag τ π q ∗ unit_tok}}};

  (* (* TODO: derive it from wfs_spec *) *)
  (* wfs_safety_spec: *)
  (*   ∀ {Σ : gFunctors} `{heap1GS Σ, invGS_gen HasNoLc Σ}, *)
  (*     wfs_mod_inv ⊢ interp m; *)
}. 
