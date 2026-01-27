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
From lawyer.nonblocking.examples.queue Require Import simple_queue_utils simple_queue.
From lawyer.nonblocking.examples.queue.dequeuer Require Import dequeuer_lib.
From heap_lang Require Import heap_lang_defs lang notation.


Close Scope Z.


Definition read_head_dequeuer (sq: SimpleQueue): val := 
  λ: <>,
    let: "ch" := !#Head in
    let: "ct" := !#Tail in
    if: "ch" = "ct" then NONE
    else SOME (get_val "ch")
.

Section ReadHeadDequeuer.      

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.
  Context {QL: QueueG Σ}.
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}. 

  Context (d: Degree).
  Context (PE: val -> iProp Σ) {PERS_PE: forall v, Persistent (PE v)}.

  Let hGS: heap1GS Σ := iem_phys _ EM.
  Existing Instance hGS.
  Definition read_head_dequeuer_fuel := 100.

  (* TODO: refactor, unify with the beginning of dequeue *)
  (* TODO: extract get_head_val_spec, remove import of dequeue.v *)
  Lemma read_head_dequeuer_spec (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ queue_inv PE ∗ dequeue_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d read_head_dequeuer_fuel }}}
       read_head_dequeuer q_sq #() @ CannotFork; NotStuck; τ; ⊤
    {{{ (v: val), RET v; th_phase_frag τ π q ∗ dequeue_token ∗ 
                         (⌜ v = NONEV ⌝ ∨ ∃ v', ⌜ v = SOMEV v' ⌝ ∗ PE v') }}}.
  Proof using PERS_PE.
    simpl. iIntros (Φ) "(#INV & TOK & PH & CPS) POST".
    rewrite /read_head_dequeuer.
    pure_steps.

    wp_bind (! _)%E.
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    
    iApply sswp_MU_wp; [done| ].
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph & %pt & HEAD & TAIL & HT & CLOS')".
    (* replace Head with (simple_queue.Head q_sq) by (by rewrite Q_SQ). *)
    iApply (wp_load with "HEAD"). iIntros "!> HEAD".
    iDestruct "DQ" as "[[%ph_ DR] | TOK']".
    2: { by iDestruct (dequeue_token_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_res_head_agree with "DR [$]") as %<-. 
    iDestruct (dequeue_resources_dangle_agree with "DR [$]") as %->.
    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".
    MU_by_burn_cp. iApply wp_value.

    iMod ("CLOS" with "[-POST CPS PH DR]") as "_".
    { by iFrame. }
    iModIntro.

    (* TODO: do we need to keep track of previous values at this point? *)
    clear t br ORDER hq.
    clear pt rop hist.

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (! _)%E.
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iApply sswp_MU_wp; [done| ].
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph_ & %pt & HEAD & TAIL & #HT & CLOS')".
    iApply (wp_load with "[$]"). iIntros "!> TAIL".
    iDestruct (dequeue_res_head_agree with "DR [$]") as %->. 
    iDestruct (dequeue_resources_auth_agree with "DR [$]") as %[<- <-].
    iDestruct (take_snapshot with "[$]") as "#SHT".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "DR DR'") as "?". }

    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".
    MU_by_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[-POST CPS PH DR]") as "_".
    { by iFrame. }
    iModIntro.

    wp_bind (Rec _ _ _)%E. pure_steps.    

    (* TODO: do we need to keep track of previous values at this point? *)
    (* clear br hob od ohv ORDER SAFE_BR hq. *)
    iClear "SHT". 
    clear hist hq od_ (* ORDER *) rop (* br *).    

    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { set_solver. }
    MU_by_burn_cp. iApply wp_value.

    (* destruct bool_decide. *)
    iDestruct "HT" as "[[%GE <-] | (%NEMPTY & %ndh & #HTH)]". 
    { assert (t = h) as ->.
      { red in ORDER. lia. }
      rewrite bool_decide_true; [| done]. 
      iApply sswp_MU_wp_fupd; [done| ]. 
      iInv "INV" as "(%hq & %h_ & %t & %br' & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
      iEval (rewrite /queue_inv_inner) in "inv".
      clear ORDER. 
      iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
      iModIntro.
      iApply sswp_pure_step; [done| ].
      do 2 iNext. MU_by_burn_cp.
      iDestruct "DQ" as "[(% & DR') | TOK]".
      { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
      iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[-> ->]. 
      iMod ("CLOS" with "[-POST CPS PH TOK]") as "_".
      { by iFrame. }
      iModIntro. pure_steps.
      iApply "POST". iFrame.
      by iLeft. }

    rewrite bool_decide_false; [| set_solver]. pure_steps.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].
  
    iApply (get_head_val_spec with "[-POST CPS]").
    { done. }
    { iFrame "#∗". }
    iIntros "!> (PH & DR & PEh)".

    iApply sswp_MU_wp_fupd; [done| ]. 
    iInv "INV" as "(%hq & %h_ & %t' & %br' & %fl_ & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".

    clear ORDER. 
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "DR DR'") as "?". }
    (* iDestruct (dequeue_res_head_agree with "DR [$]") as %->.  *)
    iDestruct (dequeue_resources_auth_agree with "DR [$]") as %[<- <-].
    iDestruct (dequeue_resources_dangle_agree with "DR [$]") as %->.

    iModIntro. iApply sswp_pure_step; [done| ]. 
    MU_by_burn_cp. simpl.
    iMod ("CLOS" with "[-POST CPS PH TOK PEh]") as "_".
    { by iFrame. }
 
    iModIntro. pure_steps.
    iApply "POST". iFrame.
    iRight. iExists _. iSplit; [done| ]. by iFrame. 
  Qed.

End ReadHeadDequeuer.
