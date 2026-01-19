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
From lawyer.nonblocking.examples.queue.dequeuer Require Import dequeuer_lib dequeue_ghost.
From heap_lang Require Import heap_lang_defs lang notation.


Close Scope Z.


Definition free_el: val :=
  λ: "nd",
    Free ("nd" +ₗ #0) ;;
    Free ("nd" +ₗ #1)
. 

Definition get_to_free '(SQ _ _ BR FL _): val :=
  λ: "ph",
    if: ("ph" = !#BR)
    then
      let: "old_fl" := !#FL in
      #FL <- "ph" ;;
      "old_fl"
    else "ph"
.

Definition dequeue '(SQ H T BR FL OHV as sq): val :=
  λ: "q",
    let: "c" := !#H in
    if: ("c" = !#T)
    then NONE
    else
      let: "v" := get_val "c" in
      #OHV <- "v" ;;
      #H <- (get_next "c") ;;
      let: "to_free" := get_to_free sq "c" in
      free_el "to_free" ;;
      (SOME "v")
.

Section Dequeue.

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.
  (* Existing Instance OHE.  *)
  Context {QL: QueueG Σ}.

  Context (d: Degree).
  Context (PE: val -> iProp Σ) {PERS_PE: forall v, Persistent (PE v)}. 

  Let hGS: heap1GS Σ := iem_phys _ EM.
  Existing Instance hGS.

  (* TODO: unify with the proof above *)
  Lemma get_head_next_spec Q τ π q h nd fl ph od:
    {{{ queue_inv PE Q ∗ ith_node h (ph, nd) ∗ dequeue_resources h fl ph od ∗
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      get_next #ph @τ
    {{{ RET #(nd.2); th_phase_frag τ π q ∗ dequeue_resources h fl ph od }}}.
  Proof using.
    simpl. iIntros (Φ) "([#QAT #INV] & #HEADhn & DR & PH & CPS) POST".
    rewrite /get_next.
    destruct nd as [v nxt]. simpl.
    pure_steps.
    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step; [done| ].
    MU_by_burn_cp. iApply wp_value.
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od' & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & >OHV & >RHI & >RH & >DQ & EI)".
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
    iApply (wp_load with "NXT"). iIntros "!> NXT". 
    MU_by_burn_cp. iApply wp_value.
    iDestruct ("CLOS'" with "[$VAL $NXT]") as "[??]".
    iMod ("CLOS" with "[-POST PH HEAD FL]") as "_".
    { by iFrame. }
    iModIntro. iApply "POST". iFrame.
  Qed.

  Lemma update_ohv_spec τ π q (v: val) l:
    {{{ queue_inv PE l ∗ th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      #(OldHeadVal q_sq) <- v @τ
    {{{ RET #(); th_phase_frag τ π q }}}.
  Proof using.
    iIntros (Φ) "([#QAT #INV] & PH & CPS) POST".
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & >OHV & >RHI & >RH & >DQ & EI)".
    iDestruct "OHV" as "(% & OHV)". 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "[$]"). iIntros "!> ?".
    MU_by_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[-POST PH]") as "_". 
    { by iFrame. }
    by iApply "POST".
  Qed.

  Lemma dequeue_upd_head_spec l τ π q h ph vh (nxh: loc) fl:
    {{{ queue_inv PE l ∗
        ith_node h (ph, (vh, nxh)) ∗ 
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel ∗
        dequeue_resources h fl ph None }}}
      #(Head q_sq) <- #nxh @τ
    {{{ RET #(); th_phase_frag τ π q ∗ dequeue_resources (h + 1) fl nxh (Some h) ∗
                   ∃ i r b, ith_read i r (h + 1) ∗ ⌜ r <= h ⌝ ∗
                               br_lb b ∗
                               (⌜ b < r ⌝ -∗ (ith_rp i rs_canceled ∨ ith_rp i rs_aborted ∨ ith_rp i (rs_proc (Some rsp_completed)))) ∗ PE vh }}}.
  Proof using.
    simpl.
    iIntros (Φ) "([#QAT #INV] & #HTH & PH & CPS & DR) POST".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & >OHV & >RHI & >RH & >DQ & EI)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-]. 
    iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->.

    iClear "INV QAT".

    (* TODO: split into lemmas *)
    iDestruct (hq_auth_lookup with "[$] [$]") as %HTH.
    iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
    { iIntros (->). iDestruct (queue_interp_cur_empty with "[$]") as %NO.
      specialize (NO 0). rewrite Nat.add_0_r in NO. congruence. }

    rewrite /dangle_interp. iDestruct "DANGLE" as "(DAUTH & [_ | (% & ?)])"; [| done].
    rewrite /dequeue_resources. iDestruct "DR" as "(CH & CFL & HEAD' & DFRAG)".
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
    rewrite /phys_queue_interp. iDestruct "PQI" as "(Q & (%pt & TAIL & DUMMY & %LL & HEAD))".
    rewrite lookup_drop Nat.add_0_r. rewrite HTH. iEval (simpl) in "HEAD".

    iCombine "HEAD HEAD'" as "HEAD". 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "[$]"). iIntros "!> [HEAD HEAD']".
    MU_by_burn_cp. iApply wp_value.
    iApply "POST". iFrame "PH". 
    iApply (dequeue_upd_head_post with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]"); eauto. 
  Qed.

  Definition dequeue_fuel := 100.    
  
  Lemma check_BR_spec l τ π q h fl ph ndh i r b0
    (READ_BOUND: r <= h):
    {{{ queue_inv PE l ∗
        ith_node h (ph, ndh) ∗
        dequeue_resources (h + 1) fl ndh.2 (Some h) ∗ 
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel ∗
        ith_read i r (h + 1) ∗ br_lb b0
    }}}
      ! #(BeingRead q_sq) @τ
    {{{ (pbr: loc), RET #pbr; th_phase_frag τ π q ∗
            dequeue_resources (h + 1) fl ndh.2 (if (decide (pbr = ph)) then Some h else None) ∗
            (⌜ pbr = ph ⌝ ∨ 
             ⌜ pbr ≠ ph ⌝ ∗ hn_interp (ph, ndh)) ∗
            ∃ b' ndbr', br_lb b' ∗ ⌜ b0 <= b' ⌝ ∗ ith_node b' (pbr, ndbr')
    }}}.
  Proof using.
    iIntros (Φ) "([#QAT #INV] & #HTH & DR& PH & CPS & #READ & #BR0) POST".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & >OHV & >RHI & >RH & >DQ & EI)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-]. 
    iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->.

    iClear "INV QAT".

    (* TODO: split into lemmas *)
    iDestruct (hq_auth_lookup with "[$] [$]") as %HTH.
    iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
    { iIntros (->). red in ORDER. lia. }

    rewrite /dangle_interp. iDestruct "DANGLE" as "(DAUTH & [% | (_ & HNI)])"; [done| ].
    rewrite Nat.add_sub HTH /=. 
    rewrite /dequeue_resources. iDestruct "DR" as "(CH & CFL & HEAD' & DFRAG)".
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
    (* rewrite /phys_queue_interp. iDestruct "PQI" as "(Q & (%pt & TAIL & DUMMY & %LL & HEAD))". *)
    iDestruct "BR" as "(%nbr & %BRTH & BR)". destruct nbr as [pbr nbr].

    iApply sswp_MU_wp; [done| ]. 
    iApply (wp_load with "BR"). iIntros "!> BR".
    MU_by_burn_cp. iApply wp_value.

    iApply "POST". iFrame.
    iApply (check_BR_post with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]"); eauto.
  Qed.

  Lemma read_FL_spec τ π l h q fl nd od:
  {{{ queue_inv PE l ∗ dequeue_resources h fl nd od ∗
      cp π d ∗ th_phase_frag τ π q }}}
    ! #(FreeLater q_sq) @τ
  {{{ (pfl: loc), RET (#pfl);
      ∃ ndfl, ith_node fl (pfl, ndfl) ∗ 
      dequeue_resources h fl nd od ∗ th_phase_frag τ π q }}}.
  Proof using.
    iIntros (Φ) "([#QAT #INV] & DR & CPS & PH) POST".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & >OHV & >RHI & >RH & >DQ & EI)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-].
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
    (* rewrite /phys_queue_interp. iDestruct "PQI" as "(Q & (%pt & TAIL & DUMMY & %LL & HEAD))". *)
    iDestruct "FL" as "(%x & %FLTH & FL & HNI_FL)". 
    iDestruct (hq_auth_get_ith with "[$]") as "#FLTH"; [by eauto| ].
    iApply sswp_MU_wp; [done| ].     
    iApply (wp_load with "FL"). iIntros "!> FL".
    rewrite cp_mul_1. 
    MU_by_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[-POST DR PH]") as "_".
    { by iFrame. }
    iModIntro. iApply "POST". iFrame.
    destruct x. iFrame "FLTH".     
  Qed.

  Lemma get_to_free_spec 
    l τ π q h fl (ph: loc) ndh i r b
    (READ_BOUND: r <= h):
    {{{ queue_inv PE l ∗
        ith_node h (ph, ndh) ∗
        dequeue_resources (h + 1) fl ndh.2 (Some h) ∗ 
        th_phase_frag τ π q ∗ cp_mul π d (get_loc_fuel + get_loc_fuel + get_loc_fuel) ∗
        ith_read i r (h + 1) ∗
        br_lb b ∗ (⌜ b < r ⌝ -∗ (ith_rp i rs_canceled ∨ ith_rp i rs_aborted ∨ ith_rp i (rs_proc (Some rsp_completed))))
    }}}
      get_to_free q_sq #ph @ τ
    {{{ (to_free: loc), RET #to_free;
        ∃ hn fl', hn_interp (to_free, hn) ∗ th_phase_frag τ π q ∗
                    dequeue_resources (h + 1) fl' ndh.2 None }}}.
  Proof using PERS_PE.    
    simpl.
    iIntros (Φ) "([#QAT #INV] & #HTH & DR& PH & CPS & #READ & #BR0 & #NO_FL) POST".
    rewrite /get_to_free. destruct q_sq eqn:Q_SQ. 
    pure_steps. 
    
    split_cps "CPS" get_loc_fuel.
    wp_bind (! _)%E. 
    replace BeingRead with (simple_queue.BeingRead q_sq) by (by rewrite Q_SQ).
    iApply (check_BR_spec with "[-POST CPS]").
    { apply READ_BOUND. }
    { iFrame "#∗". }
    iIntros "!> %pbr (PH & DR & RES)".
    iDestruct "RES" as "(RES & %b1 & %ndbr1 & #BR1 & %LEb & #BRTH1)". 

    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { set_solver. }
    MU_by_burn_cp. iApply wp_value.

    iDestruct "RES" as "[%PTR_EQ | [%NEQ HNI]]".
    2: { rewrite bool_decide_false; [| set_solver]. rewrite decide_False; [| done].
         pure_steps. iApply "POST". iFrame. }

    rewrite PTR_EQ. 

    rewrite bool_decide_true; [| set_solver]. rewrite decide_True; [| done].
    pure_steps.

    wp_bind (! _)%E.
    split_cps "CPS" 1. rewrite -cp_mul_1.
    replace FreeLater with (simple_queue.FreeLater q_sq) by (by rewrite Q_SQ).
    iApply (read_FL_spec with "[-POST CPS]").
    { iFrame "#∗". }
    iIntros "!> %pfl (%ndfl & #FLTH & DR & PH)".

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (_ <- _)%E.

    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & >OHV & >RHI & >RH & >DQ & EI)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-]. 
    iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->.

    iClear "INV QAT".

    iPoseProof (queue_interp_dangle_neq_pfl' _ _ _ _ _ ph with "QI [DANGLE]") as "#PFL_NEQ_D".
    { by rewrite Nat.add_sub. }

    rewrite /dangle_interp. iDestruct "DANGLE" as "(DAUTH & [% | (_ & HNI)])"; [done| ].

    (* TODO: split into lemmas *)
    iDestruct (hq_auth_lookup with "[$] HTH") as %HTH.
    iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
    { iIntros (->). red in ORDER. lia. }

    rewrite Nat.add_sub HTH /=. 
    rewrite /dequeue_resources. iDestruct "DR" as "(CH & CFL & HEAD' & DFRAG)".
    
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".

    iDestruct "FL" as "(%ndfl_ & %FLTH & FL & HNI_FL)".
    iDestruct (hq_auth_lookup with "[$] FLTH") as %FLTH_.
    rewrite FLTH in FLTH_. inversion FLTH_. subst ndfl_. clear FLTH_. 

    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "FL"). iIntros "!> FL".
    MU_by_burn_cp. iApply wp_value.

    iAssert (|={⊤ ∖ ↑queue_ns,⊤}=> ∃ (hn : Node) (fl' : nat),
    (let '(v, nxt) := hn in pfl ↦ v ∗ (pfl +ₗ 1) ↦ #nxt) ∗ 
    th_phase_frag τ π q ∗ @me_exact _ q_me_h (h + 1) ∗ me_exact fl' ∗
    simple_queue.Head q_sq ↦{1 / 2} #ndh.2 ∗ dangle_frag None)%I with "[-POST CPS]" as "UPD".
    2: { iMod "UPD" as "(%&%&?&PH&?&?&?&?)". iModIntro.
         wp_bind (Rec _ _ _)%E. pure_steps.
         iApply "POST". iFrame. }

    iFrame "PH".

    iApply (get_to_free_post with "HTH READ BR0 NO_FL BR1 BRTH1 FLTH PFL_NEQ_D [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]"); eauto. 
  Qed.

  Lemma free_el_spec τ π q ptr nd:
    {{{ th_phase_frag τ π q ∗ cp_mul π d (2 * get_loc_fuel) ∗ 
        hn_interp (ptr, nd) }}}
      free_el #ptr @ τ
    {{{ v, RET v; th_phase_frag τ π q }}}.
  Proof using.
    simpl. iIntros (Φ) "(PH & CPS & HN) POST".
    destruct nd. iDestruct "HN" as "[L0 L1]". 
    rewrite /free_el.
    pure_steps.

    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step; [done| ].
    MU_by_burn_cp. rewrite loc_add_0. iApply wp_value.

    wp_bind (Free _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply (wp_free with "L0"). iIntros "!> FREE0". 
    MU_by_burn_cp. iApply wp_value.
 
    wp_bind (Rec _ _ _)%E. pure_steps. 

    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step; [done| ].
    MU_by_burn_cp. iApply wp_value.

    wp_bind (Free _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply (wp_free with "[$]"). iIntros "!> FREE1". 
    MU_by_burn_cp. iApply wp_value.

    by iApply "POST". 
  Qed. 
  
  Lemma dequeue_spec l (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ queue_inv PE l ∗ dequeue_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d dequeue_fuel }}}
      dequeue q_sq l @ τ
    {{{ (v: val), RET v; th_phase_frag τ π q ∗ dequeue_token ∗
                         (∀ v', ⌜ v = SOMEV v' ⌝ -∗ PE v') }}}.
  Proof using PERS_PE.
    simpl. iIntros (Φ) "([#QAT #INV] & TOK & PH & CPS) POST".
    rewrite /dequeue. destruct q_sq eqn:Q_SQ.
    pure_steps.

    wp_bind (! _)%E.
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & >OHV & >RHI & >RH & >DQ & EI)".
    
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

    clear t br ORDER hq.
    clear pt rop hist.

    wp_bind (Rec _ _ _)%E. pure_steps. 
    
    wp_bind (! _)%E.
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & >OHV & >RHI & >RH & >DQ & EI)".
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

    (* TODO: do we need to keep track of previous values at this point? *)
    (* clear br hob od ohv ORDER SAFE_BR hq. *)
    iClear "SHT". 
    clear hist hq od_ (* ORDER *) rop (* br *).    

    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { set_solver. }
    MU_by_burn_cp. iApply wp_value.

    iDestruct "HT" as "[[%GE <-] | (%NEMPTY & %ndh & #HTH)]". 
    { assert (t = h) as ->.
      { red in ORDER. lia. }
      rewrite bool_decide_true; [| done]. 
      iApply sswp_MU_wp_fupd; [done| ]. 
      iInv "INV" as "(%hq & %h_ & %t & %br' & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
      iEval (rewrite /queue_inv_inner) in "inv".
      clear ORDER. 
      iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & >OHV & >RHI & >RH & >DQ & EI)".
      iModIntro.
      iApply sswp_pure_step; [done| ].
      do 2 iNext. MU_by_burn_cp.
      iDestruct "DQ" as "[(% & DR') | TOK]".
      { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
      iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[-> ->]. 
      iMod ("CLOS" with "[-POST CPS PH TOK]") as "_".
      { by iFrame. }
      iModIntro. pure_steps.
      iApply "POST". iFrame. by iIntros (??). }

    rewrite bool_decide_false; [| set_solver]. pure_steps.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].  
    iApply (get_head_val_spec with "[-POST CPS]").
    { done. }
    { iFrame "#∗". }
    iIntros "!> (PH & DR & PEh)".
    wp_bind (Rec _ _ _)%E. pure_steps.

    destruct ndh as [vh nxh]. simpl.
    wp_bind (_ <- _)%E.
    replace OldHeadVal with (simple_queue.OldHeadVal q_sq) by (by rewrite Q_SQ).
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].     
    iApply (update_ohv_spec with "[$QAT $PH $CPS' $INV]").
    iIntros "!> PH".
    wp_bind (Rec _ _ _)%E. pure_steps.

    split_cps "CPS" get_loc_fuel; [cbv; lia| ].
    iApply (get_head_next_spec with "[-POST CPS PEh]").
    { iFrame "#∗". }
    iIntros "!> [PH DR]". simpl.

    wp_bind (_ <- _)%E.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].
    iApply (dequeue_upd_head_spec with "[$QAT $CPS' $PH $INV $HTH $DR]").
    iIntros "!> (PH & DR & (%i & %r & %b & #ITHR & %BR & #BRB & #TOKS & PEv'))".
    (** we have two PEs here: one from reading head, another from removing head.
        Since PE is persistent, we can just drop one of them *)
    iClear "PEv'". 

    wp_bind (Rec _ _ _)%E. do 3 pure_step_cases.
    fold (get_to_free (SQ Head Tail BeingRead FreeLater OldHeadVal)).
    rewrite -Q_SQ. 
    wp_bind (get_to_free _ _)%E.         
    split_cps "CPS" (3 * get_loc_fuel); [cbv; lia| ].
    iApply (get_to_free_spec with "[-POST CPS PEh]").
    { apply BR. }
    { iFrame "#∗". }
    
    iIntros "!> %to_free (%hfr & %fl' & HNFR & PH & DR)".
    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (free_el _)%E.
    split_cps "CPS" (2 * get_loc_fuel); [cbv; lia| ].
    iApply (free_el_spec with "[CPS' PH HNFR]").
    { iFrame. }
    iIntros "!> %v PH".

    wp_bind (Rec _ _ _)%E. do 2 pure_step_cases. 
    iClear "TOKS ITHR HTH". 

    iClear "BRB". 
    clear dependent r t hfr to_free br ph b. 

    iApply sswp_MU_wp_fupd; [done| ]. 
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & >OHV & >RHI & >RH & >DQ & EI)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "DR DR'") as "?". }
    iDestruct (dequeue_resources_auth_agree with "DR [$]") as %[<- <-].
    iDestruct (dequeue_resources_dangle_agree with "DR [$]") as %->.

    iModIntro. iApply sswp_pure_step; [done| ]. 
    MU_by_burn_cp. simpl.
    iMod ("CLOS" with "[-POST CPS PH TOK PEh]") as "_".
    { by iFrame. }
 
    iModIntro. pure_steps.
    iApply "POST". iFrame.
    iIntros (? [=->]). iFrame.
  Qed.
    
End Dequeue.
