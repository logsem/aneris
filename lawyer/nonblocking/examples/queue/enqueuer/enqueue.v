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
From lawyer.nonblocking.examples.queue.enqueuer Require Import enqueuer_lib enqueue_ghost.
From heap_lang Require Import heap_lang_defs lang notation.

Close Scope Z.


Definition enqueue (sq: SimpleQueue): val :=
  λ: "v",
    let: "nd" := mk_dummy_node #() in
    let: "cl" := !#Tail in
    set_node "cl" "v" "nd" ;;
    #Tail <- "nd"
.


Section Enqueue.

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

  Definition get_loc_fuel := 5.

  Let hGS: heap1GS Σ := iem_phys _ EM.
  Existing Instance hGS.

  (** TODO: move, remove duplicates *)
  Definition mk_node_fuel := 20.

  Lemma set_node_spec (τ: locale heap_lang) (π: Phase) (q: Qp) (pt: loc) nd (v: val) (nxt: loc):
    {{{ th_phase_frag τ π q ∗ cp_mul π d mk_node_fuel ∗ hn_interp (pt, nd) }}}
       set_node #pt v #nxt @ CannotFork; NotStuck; τ; ⊤
    {{{ RET #(); th_phase_frag τ π q ∗ hn_interp (pt, (v, nxt)) }}}.
  Proof using.
    destruct nd. iIntros (Φ) "(PH & CPS & (V & NXT)) POST".
    rewrite /set_node. pure_steps.
    rewrite /set_val. pure_steps.

    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { rewrite /bin_op_eval. erewrite decide_False; [| done]. reflexivity. }
    MU_by_burn_cp. iApply wp_value.

    iApply sswp_MU_wp; [done| ].
    rewrite loc_add_0. iApply (wp_store with "V").
    iIntros "!> V".
    MU_by_burn_cp. iApply wp_value.

    wp_bind (Rec _ _ _)%E. pure_steps.
    rewrite /set_next. pure_steps.

    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { rewrite /bin_op_eval. erewrite decide_False; [| done]. reflexivity. }
    MU_by_burn_cp. iApply wp_value. 
 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "NXT").
    iIntros "!> NXT".
    MU_by_burn_cp. iApply wp_value.

    iApply "POST". iFrame.
  Qed.    

  Lemma mk_dummy_node_spec (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ th_phase_frag τ π q ∗ cp_mul π d mk_node_fuel }}}
       mk_dummy_node #() @ CannotFork; NotStuck; τ; ⊤
    {{{ (pt: loc), RET #pt; th_phase_frag τ π q ∗ hn_interp (pt, dummy_node) }}}.
  Proof using.
    iIntros (Φ) "(PH & CPS) POST". rewrite /mk_dummy_node.
    pure_steps.

    wp_bind (AllocN _ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply wp_allocN_seq.
    { lia. }
    iIntros "!>" (pt) "LS". simpl.
    iDestruct "LS" as "((V & _) & (NXT & _) & _)". 
    MU_by_burn_cp. iApply wp_value.

    wp_bind (Rec _ _ _)%E. pure_steps.
    rewrite /set_next. pure_steps.

    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { rewrite /bin_op_eval. erewrite decide_False; [| done]. reflexivity. }
    MU_by_burn_cp. iApply wp_value. 
 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "[$]").
    iIntros "!> NXT".
    MU_by_burn_cp. iApply wp_value.

    wp_bind (Rec _ _ _)%E. pure_steps.
    rewrite loc_add_0. 
    iApply "POST". iFrame.
  Qed.

  Definition enqueue_fuel := 100.

  Context (PE: val -> iProp Σ) {PERS_PE: forall v, Persistent (PE v)}.

  Lemma start_enqueue (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ queue_inv PE ∗ read_head_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d 1 }}}
       !#Tail @ CannotFork; NotStuck; τ; ⊤
    {{{ (pt: loc), RET #pt; th_phase_frag τ π q ∗ hn_interp_wip (pt, dummy_node) ∗
          ∃ (t br: nat), read_head_resources t br pt None }}}.
  Proof using.
    simpl. iIntros (Φ) "(#INV & TOK & PH & CPS) POST".
    iApply wp_atomic.
    iMod (start_enqueue_vs with "[$] [$]") as "(%pt & TAIL & TAIL')".
    iModIntro. 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_load with "TAIL"). iIntros "!> TAIL".
    MU_by_burn_cp. iApply wp_value.
    iMod ("TAIL'" with "[$]") as "(?&%&%&?)". 
    iFrame.
    iApply "POST". by iFrame.
  Qed.

  Lemma setup_cur_tail (τ: locale heap_lang) (π: Phase) (q: Qp)
    pt   t br   v nxt:
    {{{ queue_inv PE ∗ hn_interp_wip (pt, dummy_node) ∗ read_head_resources t br pt None ∗
        th_phase_frag τ π q ∗ cp_mul π d mk_node_fuel }}}
       set_node #pt v #nxt @ CannotFork; NotStuck; τ; ⊤
    {{{ RET #(); th_phase_frag τ π q ∗ hn_interp_wip (pt, (v, nxt)) ∗ read_head_resources t br pt None }}}.
  Proof using.
    simpl. iIntros (Φ) "(#INV & TNI' & RH & PH & CPS) POST".
    rewrite /set_node. pure_steps.

    rewrite /set_val. pure_steps.
    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { rewrite /bin_op_eval. erewrite decide_False; [| done]. reflexivity. }
    MU_by_burn_cp. iApply wp_value. 
    rewrite loc_add_0.

    iApply wp_atomic.
    iMod (upd_tail_value_vs with "[$] [$] [$]") as "(PT & PT')".
    iModIntro.
    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "[$]"). iIntros "!> TNI0".
    MU_by_burn_cp. iApply wp_value.
    iMod ("PT'" with "[$]") as "((TNI0 & TNI1) & RH)". 
    iModIntro.

    wp_bind (Rec _ _ _)%E. pure_steps.
    rewrite /set_next. pure_steps.

    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { rewrite /bin_op_eval. erewrite decide_False; [| done]. reflexivity. }
    MU_by_burn_cp. iApply wp_value. 
 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "TNI1"). iIntros "!> NXT".
    MU_by_burn_cp. iApply wp_value.

    iApply "POST". iFrame.    
  Qed.

  Lemma update_tail(τ: locale heap_lang) (π: Phase) (q: Qp)
    pn pt v    t br:
    {{{ queue_inv PE ∗ hn_interp (pn, dummy_node) ∗ hn_interp_wip (pt, (v, pn)) ∗ 
        read_head_resources t br pt None ∗ PE v ∗ 
        th_phase_frag τ π q ∗ cp_mul π d 1 }}}
      #Tail <- #pn @ CannotFork; NotStuck; τ; ⊤
    {{{ RET #(); th_phase_frag τ π q ∗ read_head_resources (S t) br pn None ∗ rop_token }}}.
  Proof using.
    simpl. iIntros (Φ) "(#INV & DNI & TNI & RH & PEv & PH & CPS) POST".
    iApply wp_atomic.
    iMod (update_tail_vs with "[$] [$] [$] [$] [$]") as "(TAIL & TAIL')".
    iModIntro.
    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "[$]"). iIntros "!> TAIL".
    MU_by_burn_cp. iApply wp_value.
    iMod ("TAIL'" with "[$]") as "(RH & ROP)". 
    iApply "POST". by iFrame.
  Qed.

  Lemma enqueue_spec (τ: locale heap_lang) (π: Phase) (q: Qp) (v: val):
    {{{ queue_inv PE ∗ read_head_token ∗ PE v ∗ 
        th_phase_frag τ π q ∗ cp_mul π d enqueue_fuel }}}
       enqueue q_sq v @ CannotFork; NotStuck; τ; ⊤
    {{{ RET #(); th_phase_frag τ π q ∗ read_head_token }}}.
  Proof using.
    simpl. iIntros (Φ) "(#INV & TOK & PEv & PH & CPS) POST".
    rewrite /enqueue. 
    pure_steps.

    split_cps "CPS" mk_node_fuel; [cbv; lia| ]. 
    iApply (mk_dummy_node_spec with "[$CPS' $PH]").
    iIntros "!>" (pn) "(PH & NI)".

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (! _)%E.
    split_cps "CPS" 1.
    (* replace Tail with (simple_queue.Tail q_sq) by (by rewrite Q_SQ). *)
    iApply (start_enqueue with "[$INV $CPS' $PH $TOK]").
    iIntros "!> %pt (PH & TL & (%t & %br & RH))".

    wp_bind (Rec _ _ _)%E. do 3 pure_step_cases.

    wp_bind (set_node _ _ _)%E.
    split_cps "CPS" mk_node_fuel; [cbv; lia| ]. 
    iApply (setup_cur_tail with "[$INV $CPS' $PH $TL $RH]").
    iIntros "!> (PH & TL & RH)". 
    
    wp_bind (Rec _ _ _)%E. pure_steps.
    (* rewrite Q_SQ /=.  *)
    iApply wp_fupd.
    split_cps "CPS" 1.
    iApply (update_tail with "[-POST CPS]").
    { iFrame "#∗". }

    iIntros "!> (PH & RH & ROP)".

    iMod (enqueuer_close_vs with "[$] [$] [$]") as "TOK". 
    iApply "POST". by iFrame.
  Qed.

End Enqueue.
