From iris.proofmode Require Import tactics.
From lawyer.examples Require Import orders_lib.
From lawyer.obligations Require Import env_helpers obligations_model.
From lawyer.nonblocking Require Import om_wfree_inst.
From lawyer.nonblocking.tokens Require Import logrel_tok tokens_ra.
From lawyer.nonblocking.logrel Require Import valid_client.

From trillium.program_logic Require Import weakestpre. 
From heap_lang Require Import heap_lang_defs lang notation.
From lawyer.obligations Require Import obligations_resources.

Definition method_spec_token {M} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ}
  MS {MT: MethodToken MS Σ}
    F (m: val): iProp Σ := 
  ∀ τ π q (a: val),
    {{{ cp_mul π d_wfr0 F ∗ th_phase_frag τ π q ∗ method_tok m }}}
      App m a @ τ
    {{{ v, RET v; th_phase_frag τ π q ∗ method_tok m }}}.


Definition token_safety_spec `{invGS_gen HasNoLc Σ, MethodToken MS Σ}
  {hG: heap1GS Σ}
  m: iProp Σ :=
  (* interp (method_tok m) si_add_none m *)
  (** The spec above might be provable, but our approach requires more restrictive one below.
      See the comment in op_spec_lifting *)
  □ ∀ τ v, method_tok m -∗
      let _ := @irisG_looping _ HeapLangEM _ _ hG si_add_none in
      pwp MaybeStuck ⊤ τ 
        (App (of_val m) (of_val v)) 
        (fun v => ⌜ is_ground_val v ⌝ ∗ method_tok m).


(** TODO: add the stuckness bit? *)
Record WaitFreeSpecToken (MS: gmultiset val) := {
  wfst_is_init_st: cfg heap_lang -> Prop;
  (** for wait-free modules, we expect that invariant doesn't contain OM resources *)
  wfst_mod_inv {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}: iProp Σ;
  wfst_mod_inv_Pers `{heap1GS Σ, invGS_gen HasNoLc Σ} ::
    Persistent wfst_mod_inv;
  wfst_init_mod `{heap1GS Σ, invGS_gen HasNoLc Σ, MethodTokenPre Σ}:
    forall c (INIT: wfst_is_init_st c),
      ⊢ hl_phys_init_resource c ={⊤}=∗ wfst_mod_inv ∗ 
          ∃ (_: MethodToken MS Σ), methods_toks MS;
  wfst_F: nat;
  wfst_spec:
  forall {M: Model} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ}
    {MT: MethodToken MS Σ},
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfst_mod_inv) ⊢
    [∗ set] m ∈ dom MS, method_spec_token MS wfst_F m;
    
  wfst_safety_spec:
    ∀ {Σ : gFunctors} `{heap1GS Σ, invGS_gen HasNoLc Σ, MethodToken MS Σ},
      wfst_mod_inv ⊢ [∗ set] m ∈ dom MS, token_safety_spec m;
}.
