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
From lawyer.nonblocking.examples.queue.enqueuer Require Import enqueuer_lib read_head_ghost.
From heap_lang Require Import heap_lang_defs lang notation.


Close Scope Z.


Definition get_head_val (sq: SimpleQueue): val :=
  λ: "ch1",
    let: "ch2" := !#Head in
    if: "ch1" = "ch2"
    then get_val "ch1"
    else !#OldHeadVal
.

Definition read_head_enqueuer (sq: SimpleQueue): val := 
  λ: <>,
    let: "ch" := !#Head in
    let: "ct" := !#Tail in
    if: "ch" = "ct" then NONE
    else
      #BeingRead <- "ch" ;;
      SOME (get_head_val sq "ch")
.


Section ReadHead.

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.
  (* Existing Instance OHE.  *)
  Context {QL: QueueG Σ}.
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}. 

  Context (d: Degree).
  Context (PE: val -> iProp Σ) {PERS_PE: forall v, Persistent (PE v)}. 

  Let hGS: heap1GS Σ := iem_phys _ EM.
  Existing Instance hGS.

  Definition read_head_fuel := 100.

  Lemma start_read (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ queue_inv PE ∗ read_head_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d 1 }}}
       !#Head @ CannotFork; NotStuck; τ; ⊤
    {{{ (ph: loc), RET #ph; th_phase_frag τ π q ∗ rop_token ∗ 
          ∃ t br pt rop, read_head_resources t br pt rop ∗
           (⌜ pt = ph /\ rop = None ⌝ ∨ 
            ∃ i h ndh, ⌜ pt ≠ ph /\ rop = Some i ⌝ ∗ ith_node h (ph, ndh) ∗
                        ith_read i h 0 ∗ ⌜ br <= h ⌝ ∗ disj_range h t ∗ PE ndh.1) }}}.
  Proof using PERS_PE. 
    simpl. iIntros (Φ) "(#INV & TOK & PH & CPS) POST".
    iApply wp_atomic.
    iMod (start_read_vs with "[$] [$]") as "(%ph & HEAD & HEAD')".
    iModIntro. 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_load with "HEAD"). iIntros "!> HEAD".
    MU_by_burn_cp. iApply wp_value.
    iMod ("HEAD'" with "[$]") as "X".
    iApply "POST". by iFrame.
  Qed.

  Lemma read_tail_exact (τ: locale heap_lang) (π: Phase) (q: Qp) t br pt rop:
    {{{ queue_inv PE ∗ read_head_resources t br pt rop ∗
        th_phase_frag τ π q ∗ cp_mul π d 1 }}}
       !#Tail @ CannotFork; NotStuck; τ; ⊤
    {{{ RET #pt; th_phase_frag τ π q ∗ read_head_resources t br pt rop }}}.
  Proof using.
    simpl. iIntros (Φ) "(#INV & RH & PH & CPS) POST".
    iApply wp_atomic.
    iMod (read_tail_exact_vs with "[$] [$]") as "(TAIL & TAIL')".
    iModIntro. 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_load with "TAIL"). iIntros "!> TAIL".
    MU_by_burn_cp. iApply wp_value.
    iMod ("TAIL'" with "[$]") as "RH". 
    iApply "POST". by iFrame.
  Qed.

  Lemma bump_BR (τ: locale heap_lang) (π: Phase) (q: Qp) t br pt h ndh i ph
    (BRH: br <= h):
    {{{ queue_inv PE ∗ read_head_resources t br pt (Some i) ∗
        rop_token ∗ ith_node h (ph, ndh) ∗
        ith_read i h 0 ∗
        th_phase_frag τ π q ∗ cp_mul π d 1 }}}
       #BeingRead <- #ph @ CannotFork; NotStuck; τ; ⊤
    {{{ RET #(); th_phase_frag τ π q ∗ read_head_resources t h pt (Some i) ∗ rop_token }}}.
  Proof using.
    simpl. iIntros (Φ) "(#INV & RH & RTOK & #HTH & #READ & PH & CPS) POST".
    iApply wp_atomic.
    iMod (bump_BR_vs with "[$] [$] [$] [$] [$] ") as "(%pbr0 & BR & BR')"; eauto.
    iModIntro.
    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "BR"). iIntros "!> BR". 
    MU_by_burn_cp. iApply wp_value.
    iMod ("BR'" with "[$]") as "[RH ROP]".
    iApply "POST". by iFrame.
  Qed.

  Definition small_fuel := 10.

  Lemma check_head_change (τ: locale heap_lang) (π: Phase) (q: Qp)
    t pt h ndh i ph
    (PTR_NEQ: pt ≠ ph):
    {{{ queue_inv PE ∗ read_head_resources t h pt (Some i) ∗
        rop_token ∗ ith_node h (ph, ndh) ∗
        ith_read i h 0 ∗ disj_range h t ∗ 
        cp_mul π d 1 ∗ th_phase_frag τ π q }}}
      ! #Head @ CannotFork; NotStuck; τ; ⊤
    {{{ (ph': loc), RET #ph'; 
        th_phase_frag τ π q ∗ ∃ rp, read_head_resources t h pt (Some i) ∗
          ith_rp i rp ∗ (⌜ ph' = ph /\ rp = rs_proc None ⌝ ∨ ⌜ ph' ≠ ph /\ rp = rs_canceled ⌝ ∗ rop_token ) }}}.
  Proof using.
    clear PERS_PE.
    simpl. iIntros (Φ) "(#INV & RH & TOK & #ITH & #READ & #DISJ & CPS & PH) POST".
    iApply wp_atomic.
    iMod (check_head_change_vs with "[$] [$] [$] [$] [$] [$]") as "(%ph' & HEAD & HEAD')"; eauto.
    iModIntro. 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_load with "HEAD"). iIntros "!> HEAD".
    MU_by_burn_cp. iApply wp_value.
    iMod ("HEAD'" with "[$]") as "X". 
    iApply "POST". by iFrame.
  Qed.
               
  Lemma read_ohv_spec τ π q:
    {{{ queue_inv PE ∗ th_phase_frag τ π q ∗ cp_mul π d 1 }}}
      !#OldHeadVal @ CannotFork; NotStuck; τ; ⊤
    {{{ v, RET v; th_phase_frag τ π q ∗ PE v}}}.
  Proof using PERS_PE.
    iIntros (Φ) "(#INV & PH & CPS) POST".
    iApply wp_atomic.
    iMod (read_ohv_vs with "[$]") as "(%v & OHV & OHV')".
    iModIntro. 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_load with "[$]"). iIntros "!> ?".
    MU_by_burn_cp. iApply wp_value.
    iMod ("OHV'" with "[$]") as "?". 
    iApply "POST". by iFrame.
  Qed.

  Lemma get_op_node_val_spec (τ: locale heap_lang) (π: Phase) (q: Qp)
    t h pt i ph ndh:
    {{{ queue_inv PE ∗ read_head_resources t h pt (Some i) ∗
        ith_node h (ph, ndh) ∗ ith_read i h 0 ∗ ith_rp i (rs_proc None) ∗
        cp_mul π d small_fuel ∗ th_phase_frag τ π q }}}
      get_val #ph @ CannotFork; NotStuck; τ; ⊤
    {{{ v, RET v; th_phase_frag τ π q ∗ read_head_token ∗ PE v }}}.
  Proof using PERS_PE.
    simpl. iIntros (Φ) "(#INV & RH & #ITH & #READ & #RP0 & CPS & PH) POST".
    rewrite /get_val. pure_steps.

    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step; [done| ].
    MU_by_burn_cp. rewrite loc_add_0. iApply wp_value.

    iApply wp_atomic.
    iMod (get_op_node_val_vs with "[$] [$] [$] [$] [$]") as "(%v & PPH & PPH')".
    iModIntro.
    iApply sswp_MU_wp; [done| ]. 
    iApply (wp_load with "PPH"). iIntros "!> PPH".  
    MU_by_burn_cp. iApply wp_value.
    iMod ("PPH'" with "[$]") as "X".
    iApply "POST". by iFrame.
  Qed.

  Lemma get_head_val_spec (τ: locale heap_lang) (π: Phase) (q: Qp)
    t pt h ndh i ph
    (NEQ: pt ≠ ph):
    {{{ queue_inv PE ∗ read_head_resources t h pt (Some i) ∗
        rop_token ∗ ith_node h (ph, ndh) ∗
        ith_read i h 0 ∗ disj_range h t ∗ 
        cp_mul π d (2 * small_fuel) ∗ th_phase_frag τ π q }}}
      get_head_val q_sq #ph @ CannotFork; NotStuck; τ; ⊤
    {{{ v, RET v; th_phase_frag τ π q ∗ read_head_token ∗ PE v }}}.
  Proof using PERS_PE. 
    simpl. iIntros (Φ) "(#INV & RH & TOK & #ITH & #READ & #DISJ & CPS & PH) POST".
    rewrite /get_head_val. 
    pure_steps.

    wp_bind (! _)%E.
    split_cps "CPS" 1.
    iApply (check_head_change with "[-POST CPS]").
    { apply NEQ. }
    { iFrame "#∗". }
    iIntros "!> %ph' (PH & %rp & RH & RP & CASES)".

    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ]. 
    iApply sswp_pure_step.
    { set_solver. }
    MU_by_burn_cp. iApply wp_value. 

    iDestruct "CASES" as "[(-> & ->) | ((%NEQ' & ->) & RTOK)]".
    - rewrite bool_decide_true; [| set_solver].
      pure_steps.
      split_cps "CPS" small_fuel; [cbv; lia| ]. 
      iApply (get_op_node_val_spec with "[-POST CPS]").
      { iFrame. iFrame "#∗". }
      done.
    - rewrite bool_decide_false; [| set_solver].
      pure_steps.
      split_cps "CPS" 1.
      iApply wp_fupd.      
      iApply (read_ohv_spec with "[$INV $CPS' $PH]").
      iIntros "!> % (PH & PEv)".
      iApply "POST". iFrame.      
      iApply (read_head_close_cancelled_vs with "[$] [$] [$] [$] [$] [$]").    
  Qed.

  Lemma read_head_enqueuer_spec (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ queue_inv PE ∗ read_head_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d read_head_fuel }}}
       read_head_enqueuer q_sq #() @ CannotFork; NotStuck; τ; ⊤
    {{{ (v: val), RET v; th_phase_frag τ π q ∗ read_head_token ∗
                  (⌜ v = NONEV ⌝ ∨ ∃ v', ⌜ v = SOMEV v' ⌝ ∗ PE v') }}}.
  Proof using PERS_PE.
    simpl. iIntros (Φ) "(#INV & TOK & PH & CPS) POST".
    rewrite /read_head_enqueuer. 
    pure_steps.

    wp_bind (! _)%E.
    split_cps "CPS" 1.
    iApply (start_read with "[$INV $CPS' $PH $TOK]").
    iIntros "!> %ph (PH & RTOK & (%t & %br & %pt & %rop & RH & CASES))".

    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (! _)%E.
    split_cps "CPS" 1.
    iApply (read_tail_exact with "[$INV $CPS' $PH $RH]").
    iIntros "!> (PH & RH)".

    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { set_solver. }
    MU_by_burn_cp. iApply wp_value.

    iDestruct "CASES" as "[[-> ->] | (%i & %h & %ndh & [%NEQ ->] & #ITH & #READ & %BR_H & #DISJ & PEh)]". 
    { rewrite bool_decide_true; [| done].
      iApply wp_fupd.
      pure_steps. 
      iMod (enqueuer_close_vs with "[$] [$] [$]") as "TOK".
      iApply "POST". iFrame.  
      by iLeft. }

    rewrite bool_decide_false; [| set_solver].
    pure_steps. 

    wp_bind (_ <- _)%E.
    split_cps "CPS" 1.
    iApply (bump_BR with "[-CPS POST ]").
    { apply BR_H. }
    { iFrame "#∗". }
    iIntros "!> (PH & RH & RTOK)".

    wp_bind (Rec _ _ _)%E. pure_steps.
    split_cps "CPS" (2 * small_fuel); [cbv; lia| ].
    
    wp_bind (get_head_val _ _)%E. 
    iApply (get_head_val_spec with "[-CPS POST]").
    { apply NEQ. }
    { iFrame. iFrame "#∗". }
    iIntros "!> % (PH & TOK & PEv)".

    pure_steps. iApply "POST". iFrame.
    iRight. iExists _. iSplit; [done| ]. by iFrame. 
  Qed.

End ReadHead. 
