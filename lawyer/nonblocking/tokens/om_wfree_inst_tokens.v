From iris.proofmode Require Import tactics.
From lawyer.examples Require Import orders_lib.
From lawyer.obligations Require Import env_helpers obligations_model.
From lawyer.nonblocking Require Import om_wfree_inst.
From lawyer.nonblocking.tokens Require Import logrel_tok.


From trillium.program_logic Require Import weakestpre. 
From heap_lang Require Import heap_lang_defs lang notation.
From lawyer.obligations Require Import obligations_resources.


From iris.algebra Require Import excl. 
Class MethodTokenPre Σ := {
    ut_pre_tok :: inG Σ (exclR positive);
}.
Class MethodToken Σ := {
    ut_pre_pre :: MethodTokenPre Σ;
    ut_γ: gname;
}.
Definition method_tok `{MethodToken Σ} (v: val) :=
 own ut_γ (Excl $ encode v).

Definition methods_restr := gmap val nat.

Definition method_spec_token {M} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ}
  {MT: MethodToken Σ}
    F (m: val): iProp Σ := 
  ∀ τ π q (a: val),
    {{{ cp_mul π d_wfr0 F ∗ th_phase_frag τ π q ∗ method_tok m }}}
      App m a @ τ
    {{{ v, RET v; th_phase_frag τ π q ∗ method_tok m }}}.


Record WaitFreeSpecToken (ms: methods_restr) := {
  wfst_is_init_st: cfg heap_lang -> Prop;
  (** for wait-free modules, we expect that invariant doesn't contain OM resources *)
  wfst_mod_inv {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}: iProp Σ;
  wfst_mod_inv_Pers `{heap1GS Σ, invGS_gen HasNoLc Σ} ::
    Persistent wfst_mod_inv;
  wfst_init_mod `{heap1GS Σ, invGS_gen HasNoLc Σ, MethodTokenPre Σ}:
    forall c (INIT: wfst_is_init_st c),
      ⊢ hl_phys_init_resource c ={⊤}=∗ wfst_mod_inv ∗ 
          ∃ (_: MethodToken Σ), ([∗ map] m ↦ k ∈ ms, [∗] replicate k (method_tok m));
  wfst_F: nat;
  wfst_spec:
  forall {M: Model} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ}
    {MT: MethodToken Σ},
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfst_mod_inv) ⊢
    [∗ set] m ∈ dom ms, method_spec_token wfst_F m;
    
  wfst_safety_spec:
    ∀ {Σ : gFunctors} `{heap1GS Σ, invGS_gen HasNoLc Σ, MethodToken Σ},
      wfst_mod_inv ⊢ [∗ set] m ∈ dom ms, interp (method_tok m) si_add_none m;
}.
