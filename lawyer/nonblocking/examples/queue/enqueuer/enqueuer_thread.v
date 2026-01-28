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
From lawyer.nonblocking.logrel Require Import valid_client.
From lawyer.nonblocking.examples.queue Require Import simple_queue_utils simple_queue to_int wrappers_lib.
From lawyer.nonblocking.examples.queue.enqueuer Require Import enqueue read_head.
From heap_lang Require Import heap_lang_defs lang notation.

Close Scope Z.


Definition enqueuer_thread sq: val := 
  λ: "v",
    if: "v" = #() then SOME (read_head_enqueuer sq #())
    else
      match: ToInt "v" with
        InjR "n" => SOME (enqueue sq "n")
      | InjL "x" => NONEV
      end
.


Section EnqueuerThreadLawyer.

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.
  Context {QL: QueueG Σ}.
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}. 

  Context (d: Degree).

  Definition et_fuel := max enqueue_fuel read_head_fuel + 10. 

  Let hGS: heap1GS Σ := iem_phys _ EM.
  Existing Instance hGS.
  
  From lawyer.nonblocking.logrel Require Import valid_client.

  (** The spec needed by the token-based adequacy theorem *)
  (** Note that at this point we choose the concrete predicate for queue elements,
      such that it allows to establish is_ground_val in postcondition *)
  Lemma enqueuer_thread_spec (τ: locale heap_lang) (π: Phase) (q: Qp) (v: val):
    {{{ queue_inv val_is_int ∗ read_head_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d et_fuel }}}
       enqueuer_thread q_sq v @ CannotFork; NotStuck; τ; ⊤
    {{{ (v: val), RET v; th_phase_frag τ π q ∗ read_head_token ∗
                  ⌜ is_ground_val v ⌝ }}}.
  Proof using.
    iIntros (Φ) "(#INV & TOK & PH & CPS) POST".
    rewrite /enqueuer_thread.
    pure_steps. simpl.
    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { red. set_solver. }
    MU_by_burn_cp.

    destruct (decide (v = #())) as [-> | NEQ].
    - rewrite bool_decide_true; [| done].
      pure_steps.
      split_cps "CPS" read_head_fuel; [cbv; lia| ].
      wp_bind (read_head_enqueuer _ _)%E. 
      iApply (read_head_enqueuer_spec with "[-POST CPS]").
      2: { iFrame "#∗". }
      { apply _. }
      iIntros "!> %v (PH & TOK & %RET)".
      pure_steps.
      iApply "POST". iFrame.
      iPureIntro. destruct RET as [-> | (?&->&?&->)]; by repeat constructor.
    - rewrite bool_decide_false; [| done].
      pure_steps. simpl.
      rewrite ToInt_subst. simpl.
      wp_bind (ToInt _)%E.
      iApply sswp_MU_wp.
      { apply ToInt_nval. }
      iApply sswp_pure_step; [done| ]. 
      MU_by_burn_cp.
      destruct (val_into_int_spec v) as [(?&->&->) | (NINT & ->) ].
      2: { pure_steps. wp_bind (Rec _ _ _)%E. pure_steps. 
           iApply "POST". iFrame.
           iPureIntro. repeat constructor. }
      pure_steps. wp_bind (Rec _ _ _)%E. pure_steps.
      wp_bind (enqueue _ _)%E.
      split_cps "CPS" enqueue_fuel; [cbv; lia| ].
      iApply (enqueue_spec with "[-POST CPS]").
      { iFrame "#∗". eauto. } 
      iIntros "!> (PH & TOK)".
      pure_steps. 
      iApply "POST". iFrame.
      iPureIntro. by repeat constructor.
  Qed.

End EnqueuerThreadLawyer.

From lawyer.nonblocking Require Import pwp.
From lawyer.nonblocking.examples Require Import pwp_tactics. 

 
Section EnqueuerThreadPwp.

  Context {Σ} {hG: heap1GS Σ} {invG: invGS_gen HasNoLc Σ}. 
  
  Context {QL: QueueG Σ}.
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}.

  Let iG := @irisG_looping _ HeapLangEM _ _ hG si_add_none.
  Existing Instance iG.

  (** The spec needed by the token-based adequacy theorem *)
  (** Note that at this point we choose the concrete predicate for queue elements,
      such that it allows to establish is_ground_val in postcondition *)
  (** The spec needed by the token-based adequacy theorem *)
  (** Note that at this point we choose the concrete predicate for queue elements,
      such that it allows to establish is_ground_val in postcondition *)
  Lemma enqueuer_thread_pwp_spec (τ: locale heap_lang) (v: val):
    {{{ queue_inv val_is_int ∗ read_head_token }}}
       enqueuer_thread q_sq v @ CannotFork; NotStuck; τ; ⊤
    {{{ (v: val), RET v; ⌜ is_ground_val v ⌝ ∗ read_head_token }}}.
  Proof using.
    iIntros (Φ) "(#INV & TOK) POST".
    rewrite /enqueuer_thread.

    (* TODO: pwp_pure_step gets stuck without it; fix *)
    assert (forall v, Persistent (@val_is_int Σ v)) by apply _. 

    pwp_pure_steps. simpl.
    wp_bind (_ = _)%E.
    iApply sswp_pwp; [done| ].
    iApply sswp_pure_step.
    { red. set_solver. }
    iModIntro.

    destruct (decide (v = #())) as [-> | NEQ].
    - rewrite bool_decide_true; [| done].
      pwp_pure_steps.
      iNext.
      wp_bind (read_head_enqueuer _ _)%E. 
      iApply (read_head_enqueuer_pwp_spec with "[-POST]").
      2: { iFrame "#∗". }
      { apply _. }
      iIntros "!> %v (TOK & %RET)".
      pwp_pure_steps.
      iApply "POST". iFrame.
      iPureIntro. destruct RET as [-> | (?&->&?&->)]; by repeat constructor.
    - rewrite bool_decide_false; [| done].
      pwp_pure_steps. simpl.
      rewrite ToInt_subst. simpl.
      iNext. 
      wp_bind (ToInt _)%E.
      iApply sswp_pwp.
      { apply ToInt_nval. }
      iApply sswp_pure_step; [done| ]. 
      do 2 iModIntro.
      destruct (val_into_int_spec v) as [(?&->&->) | (NINT & ->) ].
      2: { pwp_pure_steps. 
           iApply "POST". iFrame.
           iPureIntro. repeat constructor. }
      pwp_pure_steps. 
      wp_bind (enqueue _ _)%E.
      iApply (enqueue_pwp_spec with "[-POST]").
      { iFrame "#∗". eauto. } 
      iIntros "!> TOK".
      pwp_pure_steps. 
      iApply "POST". iFrame.
      iPureIntro. by repeat constructor.
  Qed.

End EnqueuerThreadPwp.
