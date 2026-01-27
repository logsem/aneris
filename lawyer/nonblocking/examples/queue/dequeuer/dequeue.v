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

Definition get_to_free (sq: SimpleQueue): val :=
  λ: "ph",
    if: ("ph" = !#BeingRead)
    then
      let: "old_fl" := !#FreeLater in
      #FreeLater <- "ph" ;;
      "old_fl"
    else "ph"
.

Definition dequeue (sq: SimpleQueue): val :=
  λ: "q",
    let: "c" := !#Head in
    if: ("c" = !#Tail)
    then NONE
    else
      let: "v" := get_val "c" in
      #OldHeadVal <- "v" ;;
      #Head <- (get_next "c") ;;
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
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}. 

  Context (d: Degree).
  Context (PE: val -> iProp Σ) {PERS_PE: forall v, Persistent (PE v)}. 

  Let hGS: heap1GS Σ := iem_phys _ EM.
  Existing Instance hGS.

  (* TODO: unify with the proof above *)
  Lemma get_head_next_spec τ π q h nd fl ph od:
    {{{ queue_inv PE ∗ ith_node h (ph, nd) ∗ dequeue_resources h fl ph od ∗
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      get_next #ph @τ
    {{{ RET #(nd.2); th_phase_frag τ π q ∗ dequeue_resources h fl ph od }}}.
  Proof using.
    simpl. iIntros (Φ) "(#INV & #HEADhn & DR & PH & CPS) POST".
    rewrite /get_next.
    destruct nd as [v nxt]. simpl.
    pure_steps.
    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step; [done| ].
    MU_by_burn_cp. iApply wp_value.
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od' & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
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

  Lemma update_ohv_spec τ π q (v: val):
    {{{ queue_inv PE ∗ th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel ∗ PE v }}}
      #OldHeadVal <- v @τ
    {{{ RET #(); th_phase_frag τ π q }}}.
  Proof using.
    iIntros (Φ) "(#INV & PH & CPS & PEv) POST".
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iDestruct "OHV" as "(% & [OHV _])". 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "[$]"). iIntros "!> ?".
    MU_by_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[-POST PH]") as "_". 
    { by iFrame. }
    by iApply "POST".
  Qed.

  (* Lemma dequeue_resources_dangle_agree h fl ph od od' h' hq': *)
  (*   dequeue_resources h fl ph od -∗ ▷ dangle_interp PE od' h' hq' -∗ ⌜ od' = od ⌝. *)
  (* Proof using. *)
  (*   simpl. iIntros "(?&?&?&FRAG) (>AUTH&?)". *)
  (*   by iDestruct (dangle_auth_frag_agree with "[$] [$]") as %?.  *)
  (* Qed. *)

  Lemma dequeue_upd_head_spec τ π q h ph vh (nxh: loc) fl:
    {{{ queue_inv PE ∗
        ith_node h (ph, (vh, nxh)) ∗ 
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel ∗
        dequeue_resources h fl ph None }}}
      #Head <- #nxh @τ
    {{{ RET #(); th_phase_frag τ π q ∗ dequeue_resources (h + 1) fl nxh (Some h) ∗
                   ∃ i r b, ith_read i r (h + 1) ∗ ⌜ r <= h ⌝ ∗
                               br_lb b ∗
                               (⌜ b < r ⌝ -∗ (ith_rp i rs_canceled ∨ ith_rp i rs_aborted ∨ ith_rp i (rs_proc (Some rsp_completed)))) }}}.
  Proof using PERS_PE.
    simpl.
    iIntros (Φ) "(#INV & #HTH & PH & CPS & DR) POST".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-].
    iAssert (▷ ⌜ od_ = None ⌝)%I with "[DR DANGLE]" as "#EQ".
    { iNext. by iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->. }
    iMod "EQ" as %->. 
    
    iClear "INV".

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
  
  Lemma check_BR_spec τ π q h fl ph ndh i r b0
    (READ_BOUND: r <= h):
    {{{ queue_inv PE ∗
        ith_node h (ph, ndh) ∗
        dequeue_resources (h + 1) fl ndh.2 (Some h) ∗ 
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel ∗
        ith_read i r (h + 1) ∗ br_lb b0
    }}}
      ! #BeingRead @τ
    {{{ (pbr: loc), RET #pbr; th_phase_frag τ π q ∗
            dequeue_resources (h + 1) fl ndh.2 (if (decide (pbr = ph)) then Some h else None) ∗
            (⌜ pbr = ph ⌝ ∨ 
             ⌜ pbr ≠ ph ⌝ ∗ hn_interp (ph, ndh) ∗ PE ndh.1) ∗
            ∃ b' ndbr', br_lb b' ∗ ⌜ b0 <= b' ⌝ ∗ ith_node b' (pbr, ndbr')
    }}}.
  Proof using PERS_PE.
    iIntros (Φ) "(#INV & #HTH & DR& PH & CPS & #READ & #BR0) POST".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-]. 
    (* iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->. *)
    iAssert (▷ ⌜ od_ = Some h ⌝)%I with "[DR DANGLE]" as "#EQ".
    { iNext. by iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->. }
    iMod "EQ" as %->. 

    iClear "INV".

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
    iDestruct "HNI" as "HNI".
    iApply (check_BR_post with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]"); eauto.
  Qed.

  Lemma read_FL_spec τ π h q fl nd od:
  {{{ queue_inv PE ∗ dequeue_resources h fl nd od ∗
      cp π d ∗ th_phase_frag τ π q }}}
    ! #FreeLater @τ
  {{{ (pfl: loc), RET (#pfl);
      ∃ ndfl, ith_node fl (pfl, ndfl) ∗ 
      dequeue_resources h fl nd od ∗ th_phase_frag τ π q }}}.
  Proof using.
    iIntros (Φ) "(#INV & DR & CPS & PH) POST".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
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
    τ π q h fl (ph: loc) ndh i r b
    (READ_BOUND: r <= h):
    {{{ queue_inv PE ∗
        ith_node h (ph, ndh) ∗
        dequeue_resources (h + 1) fl ndh.2 (Some h) ∗ 
        th_phase_frag τ π q ∗ cp_mul π d (get_loc_fuel + get_loc_fuel + get_loc_fuel) ∗
        ith_read i r (h + 1) ∗
        br_lb b ∗ (⌜ b < r ⌝ -∗ (ith_rp i rs_canceled ∨ ith_rp i rs_aborted ∨ ith_rp i (rs_proc (Some rsp_completed))))
    }}}
      get_to_free q_sq #ph @ τ
    {{{ (to_free: loc), RET #to_free;
        ∃ hn fl', hn_interp (to_free, hn) ∗ th_phase_frag τ π q ∗
                    dequeue_resources (h + 1) fl' ndh.2 None ∗ PE ndh.1 }}}.
  Proof using PERS_PE.    
    simpl.
    iIntros (Φ) "(#INV & #HTH & DR& PH & CPS & #READ & #BR0 & #NO_FL) POST".
    rewrite /get_to_free. 
    pure_steps. 
    
    split_cps "CPS" get_loc_fuel.
    wp_bind (! _)%E. 
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

    iDestruct "RES" as "[%PTR_EQ | (%NEQ & HNI & PEv)]".
    2: { rewrite bool_decide_false; [| set_solver]. rewrite decide_False; [| done].
         pure_steps. iApply "POST". iFrame. }

    rewrite PTR_EQ. 

    rewrite bool_decide_true; [| set_solver]. rewrite decide_True; [| done].
    pure_steps.

    wp_bind (! _)%E.
    split_cps "CPS" 1. rewrite -cp_mul_1.
    iApply (read_FL_spec with "[-POST CPS]").
    { iFrame "#∗". }
    iIntros "!> %pfl (%ndfl & #FLTH & DR & PH)".

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (_ <- _)%E.

    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & #EI)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-]. 
    (* iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->. *)
    iAssert (▷ ⌜ od_ = Some h ⌝)%I with "[DR DANGLE]" as "#EQ".
    { iNext. by iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->. }
    iMod "EQ" as %->. 

    iClear "INV".

    iPoseProof (queue_interp_dangle_neq_pfl' _ _ _ _ _ ph with "QI [DANGLE]") as "#PFL_NEQ_D".
    { by rewrite Nat.add_sub. }

    rewrite /dangle_interp. iDestruct "DANGLE" as "(DAUTH & [% | (_ & HNI)])"; [done| ].

    (* TODO: split into lemmas *)
    iDestruct (hq_auth_lookup with "[$] HTH") as %HTH.
    iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
    { iIntros (->). red in ORDER. lia. }

    rewrite Nat.add_sub HTH /=. 
    rewrite /dequeue_resources. iDestruct "DR" as "(CH & CFL & HEAD' & DFRAG)".
    iDestruct "HNI" as "HNI". 
    
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".

    iDestruct "FL" as "(%ndfl_ & %FLTH & FL & HNI_FL)".
    iDestruct (hq_auth_lookup with "[$] FLTH") as %FLTH_.
    rewrite FLTH in FLTH_. inversion FLTH_. subst ndfl_. clear FLTH_. 

    iApply sswp_MU_wp; [done| ].                  
    
    iApply (wp_store with "FL"). iIntros "!> FL".
    MU_by_burn_cp. iApply wp_value.

    iDestruct (queue_elems_interp_get _ _ h with "EI") as "PEv"; eauto. 

    iAssert (|={⊤ ∖ ↑queue_ns,⊤}=> ∃ (hn : Node) (fl' : nat),
    (let '(v, nxt) := hn in pfl ↦ v ∗ (pfl +ₗ 1) ↦ #nxt) ∗ 
    th_phase_frag τ π q ∗ @me_exact _ q_me_h (h + 1) ∗ me_exact fl' ∗
    simple_queue.Head ↦{1 / 2} #ndh.2 ∗ dangle_frag None)%I with "[-POST CPS PEv]" as "UPD".
    2: { iMod "UPD" as "(%&%&?&PH&?&?&?&?)". iModIntro.
         wp_bind (Rec _ _ _)%E. pure_steps.
         iApply "POST". iFrame. done. }

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
  
  Lemma dequeue_spec (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ queue_inv PE ∗ dequeue_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d dequeue_fuel }}}
      dequeue q_sq #() @ τ
    {{{ (v: val), RET v; th_phase_frag τ π q ∗ dequeue_token ∗
                         (⌜ v = NONEV ⌝ ∨ ∃ v', ⌜ v = SOMEV v' ⌝ ∗ PE v') }}}.
  Proof using PERS_PE.
    simpl. iIntros (Φ) "(#INV & TOK & PH & CPS) POST".
    rewrite /dequeue. 
    pure_steps.

    wp_bind (! _)%E.
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    
    iApply sswp_MU_wp; [done| ].
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph & %pt & HEAD & TAIL & HT & CLOS')".
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
      iApply "POST". iFrame. by iLeft. }

    rewrite bool_decide_false; [| set_solver]. pure_steps.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].  
    iApply (get_head_val_spec with "[-POST CPS]").
    { done. }
    { iFrame "#∗". }
    iIntros "!> (PH & DR & PEh)".
    wp_bind (Rec _ _ _)%E. pure_steps.

    destruct ndh as [vh nxh]. simpl.
    wp_bind (_ <- _)%E.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].
    iApply (update_ohv_spec with "[$PH $CPS' $INV $PEh]").
    iIntros "!> PH".
    wp_bind (Rec _ _ _)%E. pure_steps.

    split_cps "CPS" get_loc_fuel; [cbv; lia| ].
    iApply (get_head_next_spec with "[-POST CPS]").
    { iFrame "#∗". }
    iIntros "!> [PH DR]". simpl.

    wp_bind (_ <- _)%E.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].
    iApply (dequeue_upd_head_spec with "[$CPS' $PH $INV $HTH $DR]").
    iIntros "!> (PH & DR & (%i & %r & %b & #ITHR & %BR & #BRB & #TOKS))".

    wp_bind (Rec _ _ _)%E. do 3 pure_step_cases.
    fold (get_to_free (SQ Head Tail BeingRead FreeLater OldHeadVal)).
    wp_bind (get_to_free _ _)%E.         
    split_cps "CPS" (3 * get_loc_fuel); [cbv; lia| ].
    iApply (get_to_free_spec with "[-POST CPS]").
    { apply BR. }
    { iFrame "#∗". }
    
    iIntros "!> %to_free (%hfr & %fl' & HNFR & PH & DR & PEv)".
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
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "DR DR'") as "?". }

    iModIntro. iApply sswp_pure_step; [done| ].
    iNext. 
    iDestruct (dequeue_resources_auth_agree with "DR [$]") as %[<- <-].
    MU_by_burn_cp. simpl.
    iMod ("CLOS" with "[-POST CPS PH TOK PEv]") as "_".
    { by iFrame. }
 
    iModIntro. pure_steps.
    iApply "POST". iFrame.
    iRight. iExists _. iSplit; [done| ]. by iFrame. 
  Qed.
    
End Dequeue.
