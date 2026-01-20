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
From heap_lang Require Import heap_lang_defs lang notation.

Close Scope Z.

Section RightUtils.

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.
  (* Existing Instance OHE.  *)
  Context {QL: QueueG Σ}.

  Context (d: Degree).

  Context (PE: val -> iProp Σ) {PERS_PE: forall v, Persistent (PE v)}. 

  Definition get_loc_fuel := 5.

  Let hGS: heap1GS Σ := iem_phys _ EM.
  Existing Instance hGS.

  Lemma get_head_val_spec Q τ π q h nd fl ph od:
    {{{ queue_inv PE Q ∗ ith_node h (ph, nd) ∗ dequeue_resources h fl ph od ∗
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      get_val #ph @τ
    {{{ RET (nd.1); th_phase_frag τ π q ∗ dequeue_resources h fl ph od ∗ PE nd.1 }}}.
  Proof using PERS_PE.
    simpl. iIntros (Φ) "([#QAT #INV] & #HEADhn & DR & PH & CPS) POST".
    rewrite /get_val.
    destruct nd as [v nxt]. simpl.
    pure_steps.
    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step; [done| ].
    MU_by_burn_cp. rewrite loc_add_0. iApply wp_value.
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & #EI)".
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-].
    iDestruct "DR" as "[HEAD FL]".
    iDestruct (hq_auth_lookup with "[$] [$]") as %HTH.
    iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
    { iIntros (->). iDestruct (queue_interp_cur_empty with "[$]") as %NO.
      specialize (NO 0). rewrite Nat.add_0_r in NO. congruence. }
    iDestruct (access_queue with "[$] [$] [$]") as "[HNI CLOS']".
    { red in ORDER. lia. }
    rewrite {1}/hn_interp. iDestruct "HNI" as "[VAL NXT]".
    iApply sswp_MU_wp; [done| ].
    iApply (wp_load with "VAL"). iIntros "!> VAL". 
    MU_by_burn_cp. iApply wp_value.
    iDestruct ("CLOS'" with "[$VAL $NXT]") as "[? HQ]".

    iDestruct (queue_elems_interp_get with "[$]") as "PEv"; eauto. 
      
    iMod ("CLOS" with "[-POST PH HEAD FL PEv]") as "_".
    { iFrame. by iFrame "EI". }
    iModIntro. iApply "POST". iFrame.
  Qed.

End RightUtils.
