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
From lawyer.nonblocking.examples.queue Require Import simple_queue_utils simple_queue dequeue read_head.
From heap_lang Require Import heap_lang_defs lang notation.


Close Scope Z.


Section OtherMethods.

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.
  (* Existing Instance OHE.  *)
  Context {QL: QueueG Σ}.

  Definition read_head_dequeuer: val := 
    λ: <>,
      let: "ch" := !#(Head q_sq) in
      let: "ct" := !#(Tail q_sq) in
      if: "ch" = "ct" then NONE
      else SOME (get_val "ch")
  .

  Context (d: Degree).

  Definition get_loc_fuel := 5.

  Let hGS: heap1GS Σ := iem_phys _ EM.
  Existing Instance hGS.

  Definition set_val: val := λ: "nd" "v", ("nd" +ₗ #0) <- "v".
  Definition set_next: val := λ: "nd" "nxt", ("nd" +ₗ #1) <- "nxt".

  Definition set_node: val := 
      λ: "nd" "v" "nxt",
        set_val "nd" "v" ;;
        set_next "nd" "nxt"
  .

  Definition mk_dummy_node: val :=
    λ: <>,
      (** dummy node has concrete field values, so we have to set them *)
      let: "nd" := AllocN (Val $ LitV $ LitInt 2) #0 in
      set_next "nd" #(Loc 0) ;;
      "nd"
  .

  Definition enqueue '(SQ H T BR FL OHV as sq): val :=
    λ: "v",
      let: "nd" := mk_dummy_node #() in
      let: "cl" := !#T in
      set_node "cl" "v" "nd" ;;
      #T <- "nd"
  .

  (** TODO: move, remove duplicates *)
  Definition mk_node_fuel := 20.

  Lemma set_node_spec (τ: locale heap_lang) (π: Phase) (q: Qp) (pt: loc) nd (v: val) (nxt: loc):
    {{{ th_phase_frag τ π q ∗ cp_mul π d mk_node_fuel ∗ hn_interp (pt, nd) }}}
       set_node #pt v #nxt @τ
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
       mk_dummy_node #() @τ
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

  Lemma start_enqueue l (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ queue_inv l ∗ read_head_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d 1 }}}
       !#(Tail q_sq) @ τ
    {{{ (pt: loc), RET #pt; th_phase_frag τ π q ∗ rop_token ∗ 
          ∃ t br rop, read_head_resources t br pt rop }}}.
  Proof using.
    simpl. iIntros (Φ) "([#QAT #INV] & TOK & PH & CPS) POST".
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER0 & QI & DANGLE & OHV & RHI & RH & DQ)".
    
    iApply sswp_MU_wp; [done| ].
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph & %pt & HEAD & TAIL & #HT & CLOS')".    
    iApply (wp_load with "TAIL"). iIntros "!> TAIL".
    iDestruct "RH" as "[(%pt_ & RH & RTOK) | TOK']".
    2: { by iDestruct (read_head_token_excl with "[$] [$]") as "?". }
    iDestruct (read_head_res_Tail_agree with "RH [$]") as %EQ.
    inversion EQ. subst pt_. clear EQ. 
      
    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".
    MU_by_burn_cp. iApply wp_value.

    iApply "POST". iFrame.

    iMod ("CLOS" with "[-]") as "_"; [| done].
    by iFrame.
  Qed.    

  Lemma enqueue_spec l (τ: locale heap_lang) (π: Phase) (q: Qp) (v: val):
    {{{ queue_inv l ∗ read_head_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d enqueue_fuel }}}
       enqueue q_sq l v @ τ
    {{{ (v: val), RET v; th_phase_frag τ π q ∗ read_head_token }}}.
  Proof using.
    simpl. iIntros (Φ) "([#QAT #INV] & TOK & PH & CPS) POST".
    rewrite /enqueue. destruct q_sq eqn:Q_SQ.
    pure_steps.

    split_cps "CPS" mk_node_fuel; [cbv; lia| ]. 
    iApply (mk_dummy_node_spec with "[$CPS' $PH]").
    iIntros "!>" (pn) "(PH & NI)".

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (! _)%E.
    split_cps "CPS" 1.
    replace Tail with (simple_queue.Tail q_sq) by (by rewrite Q_SQ).
    iApply (start_enqueue with "[$QAT $INV $CPS' $PH $TOK]").
    iIntros "!> %pt (PH & RTOK & (%t & %br & %rop & RH))".

    wp_bind (Rec _ _ _)%E. do 3 pure_step_cases.

    wp_bind (set_node _ _ _)%E.
    split_cps "CPS" mk_node_fuel; [cbv; lia| ]. 
    iApply (set_node_spec with "[$CPS' $PH NI]").
    { 

    
    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { set_solver. }
    MU_by_burn_cp. iApply wp_value.



    

      

  Definition read_head_dequeuer_fuel := 100.

  (* TODO: refactor, unify with the beginning of dequeue *)
  (* TODO: extract get_head_val_spec, remove import of dequeue.v *)
  Lemma read_head_dequeuer_spec l (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ queue_inv l ∗ dequeue_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d read_head_dequeuer_fuel }}}
       read_head_dequeuer #() @ τ
    {{{ (v: val), RET v; th_phase_frag τ π q ∗ dequeue_token }}}.
  Proof using.
    simpl. iIntros (Φ) "([#QAT #INV] & TOK & PH & CPS) POST".
    rewrite /read_head_dequeuer. destruct q_sq eqn:Q_SQ.
    pure_steps.

    wp_bind (! _)%E.
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER & QI & DANGLE & OHV & RHI & RH & DQ)".
    
    iApply sswp_MU_wp; [done| ].
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph & %pt & HEAD & TAIL & HT & CLOS')".
    replace Head with (simple_queue.Head q_sq) by (by rewrite Q_SQ).
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
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER & QI & DANGLE & OHV & RHI & RH & DQ)".
    iApply sswp_MU_wp; [done| ].
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph_ & %pt & HEAD & TAIL & #HT & CLOS')".
    replace Tail with (simple_queue.Tail q_sq) by (by rewrite Q_SQ).
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
      iDestruct "inv" as ">(HQ & AUTHS & %ORDER & QI & DANGLE & OHV & RHI & RH & DQ)".
      iModIntro.
      iApply sswp_pure_step; [done| ].
      do 2 iNext. MU_by_burn_cp.
      iDestruct "DQ" as "[(% & DR') | TOK]".
      { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
      iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[-> ->]. 
      iMod ("CLOS" with "[-POST CPS PH TOK]") as "_".
      { by iFrame. }
      iModIntro. pure_steps.
      iApply "POST". iFrame. }

    rewrite bool_decide_false; [| set_solver]. pure_steps.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].  
    iApply (get_head_val_spec with "[-POST CPS]").
    { iFrame "#∗". }
    iIntros "!> [PH DR]".

    iApply sswp_MU_wp_fupd; [done| ]. 
    iInv "INV" as "(%hq & %h_ & %t' & %br' & %fl_ & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER' & QI & DANGLE & OHV & RHI & RH & DQ)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "DR DR'") as "?". }
    (* iDestruct (dequeue_res_head_agree with "DR [$]") as %->.  *)
    iDestruct (dequeue_resources_auth_agree with "DR [$]") as %[<- <-].
    iDestruct (dequeue_resources_dangle_agree with "DR [$]") as %->.

    iModIntro. iApply sswp_pure_step; [done| ]. 
    MU_by_burn_cp. simpl.
    iMod ("CLOS" with "[-POST CPS PH TOK]") as "_".
    { by iFrame. }
 
    iModIntro. pure_steps.
    iApply "POST". iFrame.
  Qed.    

End OtherMethods.
