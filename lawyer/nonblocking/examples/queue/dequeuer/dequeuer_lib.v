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


Section GetHeadValViewshifts.
  Context {Σ} {hG: heap1GS Σ} {invG: invGS_gen HasNoLc Σ}.   
  Context {QL: QueueG Σ}.
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}.
  Context (PE: val -> iProp Σ) {PERS_PE: forall v, Persistent (PE v)}.

  Lemma dequeuer_read_head_vs:
    queue_inv PE -∗ dequeue_token -∗
    |={⊤, ⊤ ∖ ↑queue_ns}=> ∃ h (ph: loc) fl,
      Head ↦{1/2} #ph ∗ ▷ (Head ↦{1/2} #ph -∗ |={⊤ ∖ ↑queue_ns, ⊤}=> dequeue_resources h fl ph None).
  Proof using.
    iIntros "#INV TOK".
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iModIntro.
    
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph & %pt & HEAD & TAIL & HT & CLOS')".
    iFrame "HEAD".
    iExists _, _. iIntros "!> HEAD".
    iDestruct "DQ" as "[[%ph_ DR] | TOK']".
    2: { by iDestruct (dequeue_token_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_res_head_agree with "DR [$]") as %<-. 
    iDestruct (dequeue_resources_dangle_agree with "DR [$]") as %->.
    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".
    iFrame "DR". 

    iMod ("CLOS" with "[-]") as "_"; [| done].
    by iFrame.
  Qed.    

  Lemma dequeuer_read_tail_vs h fl ph:
    queue_inv PE -∗ dequeue_resources h fl ph None -∗ 
    |={⊤, ⊤ ∖ ↑queue_ns}=> ∃ t br (pt: loc),
      Tail ↦{1 / 2} #pt ∗ ⌜ hq_state_wf h t br fl ⌝ ∗ 
      (⌜h ≥ t ∧ ph = pt⌝ ∨ ⌜h < t ∧ ph ≠ pt⌝ ∗ (∃ nd, ith_node h (ph, nd))) ∗
      ▷ (Tail ↦{1 / 2} #pt -∗ |={⊤∖↑queue_ns, ⊤}=> dequeue_resources h fl ph None).
  Proof using.
    iIntros "#INV DR".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iModIntro.
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph_ & %pt & HEAD & TAIL & #HT & CLOS')".
    iFrame "TAIL".
    iDestruct (dequeue_res_head_agree with "DR [$]") as %->. 
    iDestruct (dequeue_resources_auth_agree with "DR [$]") as %[<- <-].
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "DR DR'") as "?". }
    iFrame (ORDER). iFrame "HT".
    iIntros "!> TAIL".
    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".
    iMod ("CLOS" with "[-DR]") as "_".
    { by iFrame. }
    by iFrame. 
  Qed.

  Lemma dequeuer_close h fl ph:
    queue_inv PE -∗ dequeue_resources h fl ph None ={⊤}=∗ dequeue_token.
  Proof using.
    iIntros "#INV DR".
    iInv "INV" as "(%hq & %h_ & %t & %br' & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[-> ->]. 
    iMod ("CLOS" with "[-TOK]") as "_".
    { by iFrame. }
    by iFrame.
  Qed.

  Lemma get_head_val_vs h nd fl ph od:
    queue_inv PE -∗ ith_node h (ph, nd) -∗
    dequeue_resources h fl ph od -∗
    |={⊤, ⊤∖↑queue_ns}=> ph ↦ nd.1 ∗ ▷ (ph ↦ nd.1 -∗ (PE nd.1 ∗ |={⊤∖↑queue_ns, ⊤}=> dequeue_resources h fl ph od)).
  Proof using PERS_PE. 
    iIntros "#INV #HEADhn DR".
    destruct nd as [v nxt]. simpl.
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & #EI)".
    iModIntro.
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-].
    iDestruct "DR" as "[HEAD FL]".
    iDestruct (hq_auth_lookup with "[$] [$]") as %HTH.
    iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
    { iIntros (->). iDestruct (queue_interp_cur_empty with "[$]") as %NO.
      specialize (NO 0). rewrite Nat.add_0_r in NO. congruence. }

    iDestruct (access_queue with "[$] [$] [$]") as "[HNI CLOS']".
    { red in ORDER. lia. }
    rewrite {1}/hn_interp. iDestruct "HNI" as "[VAL NXT]".
    iFrame "VAL".
    iIntros "!> VAL". 
    iDestruct ("CLOS'" with "[$VAL $NXT]") as "[? HQ]".

    iDestruct (queue_elems_interp_get with "[$]") as "PEv"; eauto.
    iFrame "PEv". 

    iMod ("CLOS" with "[-HEAD FL]") as "_".
    { iFrame. by iFrame "EI". }
    iModIntro. iFrame.
  Qed.

End GetHeadValViewshifts.


Section GetHeadValLawyer.

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

  Definition get_loc_fuel := 5.

  Let hGS: heap1GS Σ := iem_phys _ EM.
  Existing Instance hGS.

  Lemma get_head_val_spec τ π q h nd fl ph od:
    {{{ queue_inv PE ∗ ith_node h (ph, nd) ∗ dequeue_resources h fl ph od ∗
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      get_val #ph @ CannotFork; NotStuck; τ; ⊤
    {{{ RET (nd.1); th_phase_frag τ π q ∗ dequeue_resources h fl ph od ∗ PE nd.1 }}}.
  Proof using PERS_PE.
    simpl. iIntros (Φ) "(#INV & #HEADhn & DR & PH & CPS) POST".
    rewrite /get_val.
    destruct nd as [v nxt]. simpl.
    pure_steps.
    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step; [done| ].
    MU_by_burn_cp. rewrite loc_add_0. iApply wp_value.

    iMod (get_head_val_vs with "[$] [$] [$]") as "(VAL & VAL')".
    iApply sswp_MU_wp; [done| ].
    iApply (wp_load with "VAL"). iIntros "!> VAL".
    iDestruct ("VAL'" with "[$]") as "(#PEv & CLOS)". 
    MU_by_burn_cp. iApply wp_value.
    iMod "CLOS" as "DR". iModIntro. 
    iApply "POST". iFrame "#∗". 
  Qed.

End GetHeadValLawyer.


From lawyer.nonblocking Require Import pwp.
From lawyer.nonblocking.examples Require Import pwp_tactics. 

Section GetHeadValPwp.
  Context {Σ} {hG: heap1GS Σ} {invG: invGS_gen HasNoLc Σ}. 
  
  Context {QL: QueueG Σ}.
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}.

  Context (PE: val -> iProp Σ) {PERS_PE: forall v, Persistent (PE v)}.

  Let iG := @irisG_looping _ HeapLangEM _ _ hG si_add_none.
  Existing Instance iG.

  Lemma get_head_val_pwp_spec τ h nd fl ph od:
    {{{ queue_inv PE ∗ ith_node h (ph, nd) ∗ dequeue_resources h fl ph od }}}
      get_val #ph @ CannotFork; NotStuck; τ; ⊤
    {{{ RET (nd.1); dequeue_resources h fl ph od ∗ PE nd.1 }}}.
  Proof using PERS_PE.
    simpl. iIntros (Φ) "(#INV & #HEADhn & DR) POST".
    rewrite /get_val.
    destruct nd as [v nxt]. simpl.
    pwp_pure_steps.
    wp_bind (_ +ₗ _)%E.
    iApply sswp_pwp; [done| ].
    iApply sswp_pure_step; [done| ].
    do 2 iModIntro. rewrite loc_add_0. iApply wp_value.

    iApply wp_atomic.
    iMod (get_head_val_vs with "[$] [$] [$]") as "(VAL & VAL')".
    iApply sswp_pwp; [done| ]. iModIntro. 
    iApply (wp_load with "VAL"). iIntros "!> VAL".
    iDestruct ("VAL'" with "[$]") as "(#PEv & CLOS)". 
    iModIntro. iApply wp_value.
    iMod "CLOS" as "DR". iModIntro. 
    iApply "POST". iFrame "#∗". 
  Qed.

End GetHeadValPwp.
