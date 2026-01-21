From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import utils.
From lawyer.examples Require Import obls_tactics.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From lawyer.nonblocking.examples.queue Require Import simple_queue_utils simple_queue is_int.
From lawyer.nonblocking.examples.queue.enqueuer Require Import enqueue read_head.
From heap_lang Require Import heap_lang_defs lang notation.

Close Scope Z.


Section EnqueuerThread.

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.
  Context {QL: QueueG Σ}.

  Definition enqueuer_thread: val := 
    λ: "v",
      if: "v" = #() then SOME (read_head_enqueuer #())
      else
        match: "v" with
          InjL "n" => SOME (enqueue q_sq "n")
        | InjR "x" => NONEV
        end.

  Context (d: Degree).

  Definition et_fuel := max enqueue_fuel read_head_fuel + 10. 

  Let hGS: heap1GS Σ := iem_phys _ EM.
  Existing Instance hGS.

  (* TODO: move *)
  Definition val_is_int (v: val): iProp Σ := ⌜ ∃ (n: Z), v = #n ⌝.
  
  From lawyer.nonblocking.logrel Require Import valid_client.

  (** The spec needed by the token-based adequacy theorem *)
  Lemma read_head_enqueuer_spec l (τ: locale heap_lang) (π: Phase) (q: Qp) (v: val):
    {{{ queue_inv val_is_int l ∗ read_head_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d et_fuel }}}
       enqueuer_thread v @ τ
    {{{ (v: val), RET v; th_phase_frag τ π q ∗ read_head_token ∗
                  ⌜ is_ground_val v ⌝ }}}.
  Proof using.
    
    
  Admitted. 

End EnqueuerThread. 
