From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import utils.
From lawyer.examples Require Import obls_tactics.
From lawyer.nonblocking.examples Require Import simple_queue_utils simple_queue.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


Close Scope Z.


Section Dequeue.

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.
  (* Existing Instance OHE.  *)
  Context {QL: QueueG Σ}.

  Context (d: Degree).

  Definition get_loc_fuel := 5.

  Let hGS: heap1GS Σ := iem_phys _ EM.
  Existing Instance hGS. 

  Lemma get_head_val_spec Q τ π q h nd fl ph od:
    {{{ queue_inv Q ∗ ith_node h (ph, nd) ∗ dequeue_resources h fl ph od ∗
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      get_val #ph @τ
    {{{ RET (nd.1); th_phase_frag τ π q ∗ dequeue_resources h fl ph od }}}.
  Proof using.
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
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER & QI & DANGLE & OHV & RHI & RH & DQ)".
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
    iDestruct ("CLOS'" with "[$VAL $NXT]") as "[??]".
    iMod ("CLOS" with "[-POST PH HEAD FL]") as "_".
    { by iFrame. }
    iModIntro. iApply "POST". iFrame.
  Qed.

  (* TODO: unify with the proof above *)
  Lemma get_head_next_spec Q τ π q h nd fl ph od:
    {{{ queue_inv Q ∗ ith_node h (ph, nd) ∗ dequeue_resources h fl ph od ∗
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
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER & QI & DANGLE & OHV & RHI & RH & DQ)".
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
    {{{ queue_inv l ∗ th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      #(OldHeadVal q_sq) <- v @τ
    {{{ RET #(); th_phase_frag τ π q }}}.
  Proof using.
    iIntros (Φ) "([#QAT #INV] & PH & CPS) POST".
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER & QI & DANGLE & OHV & RHI & RH & DQ)".
    iDestruct "OHV" as "(% & OHV)". 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "[$]"). iIntros "!> ?".
    MU_by_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[-POST PH]") as "_". 
    { by iFrame. }
    by iApply "POST".
  Qed.

  Lemma is_LL_into_drop hq pt k
    (LL: is_LL_into hq pt):
    is_LL_into (drop k hq) pt.
  Proof using.
    revert k. induction hq.
    { intros. by rewrite drop_nil. }
    intros. destruct k.
    { by rewrite drop_0. }
    simpl. apply IHhq.
    simpl in LL. destruct a as [? [? ?]].
    destruct hq; try done.
    destruct h as [? [? ?]]. tauto.
  Qed.

  Lemma dom_max_set_fold n:
    set_fold max 0 (set_seq 0 (S n): gset nat) = n.
  Proof using.
    clear. induction n.
    { done. }
    rewrite set_seq_S_end_union_L.
    rewrite union_comm_L. 
    erewrite set_fold_union.
    2-4: red; lia.
    simpl. rewrite IHn.
    rewrite set_fold_singleton. lia.
  Qed.

  Definition upd_rp rp :=
    match rp with
    | rs_init => rs_canceled
    | rs_proc (Some rsp_going) => rs_proc (Some rsp_protected)
    | _ => rp
    end. 

  Lemma upd_rp_rs_step p: rs_step p (upd_rp p).
  Proof using.
    destruct p; simpl; try constructor.
    destruct orsp; simpl; try constructor.
    destruct r; repeat constructor.
  Qed.

  Lemma read_hist_wf_bump (hist: read_hist) rop h rp
    (RH_WF: read_hist_wf hist rop h)
    (n := set_fold max 0 (dom hist)):
    read_hist_auth hist -∗ ith_rp n rp ==∗
    ∃ r rp', let hist' := <[ n := ((r, h + 1), rp') ]> hist in
      read_hist_auth hist' ∗ ith_read n r (h + 1) ∗ ⌜ read_hist_wf hist' rop (h + 1) ⌝ ∗
      ith_rp n (upd_rp rp) ∗ ⌜ r <= h ⌝.
  Proof using.
    rewrite /read_hist_wf. iIntros "AUTH RP".
    destruct RH_WF as (n_ & DOM & ROP & SEQ & BB).

    assert (n_ = n) as ->.
    { subst n. rewrite DOM. by rewrite dom_max_set_fold. }

    destruct (hist !! n) as [[[r b0] p]| ] eqn:NTH.
    2: { apply not_elem_of_dom in NTH. rewrite DOM in NTH.
         rewrite elem_of_set_seq in NTH. lia. }
    iDestruct (ith_rp_hist_compat with "[$] [$]") as %(? & ? & EQ').
    rewrite NTH in H. inversion H. subst x. simpl in EQ'. clear H.
    rename rp into p_. 
    
    iMod (read_hist_update' _ _ _ _ _ (h + 1) with "AUTH RP") as "(AUTH & #ITH & RP)".
    { apply upd_rp_rs_step. }
    { apply NTH. }

    rewrite Nat.max_r.
    2: { apply BB in NTH. simpl in NTH. lia. }
    iModIntro. do 2 iExists _. iFrame "AUTH ITH RP".
    iPureIntro. split.
    2: { eapply BB in NTH; eauto. by apply NTH. }

    exists n. split; [| split; [| split]]. 
    - rewrite dom_insert_L. apply mk_is_Some, elem_of_dom in NTH. set_solver.
    - done.
    - intros ?????. rewrite !lookup_insert_Some.
      intros [(? & ?) | (? & ITH) ] [(? & ?) | (? & JTH) ]; subst; simpl in *; try lia.
      + apply mk_is_Some, elem_of_dom in JTH.
        rewrite DOM elem_of_union elem_of_set_seq elem_of_singleton in JTH. lia.
      + eapply SEQ in H; eauto. done.
      + eapply SEQ; eauto.
    - intros ??. rewrite lookup_insert_Some.         
      intros [(? & ?) | (? & ITH) ]; subst; simpl; try lia.
      { eapply BB in NTH; eauto. simpl in NTH. lia. }
      eapply BB in ITH; eauto. lia.
  Qed.

  Lemma upd_rp_fin_pres rs
    (FIN: rs_fin rs):
    rs_fin (upd_rp rs).
  Proof using.
    red. destruct FIN; subst; simpl; try by eauto.
    destruct H; subst; try by eauto.
  Qed.
  
  Lemma drop_drop_comm: ∀ {A : Type} (l : list A) (n1 n2 : nat),
      drop n1 (drop n2 l) = drop n2 (drop n1 l).
  Proof using.
    intros. rewrite !drop_drop. f_equal. lia.
  Qed.

  Lemma dequeue_upd_head_spec l τ π q h ph vh (nxh: loc) fl:
    {{{ queue_inv l ∗
        ith_node h (ph, (vh, nxh)) ∗ 
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel ∗
        dequeue_resources h fl ph None }}}
      #(Head q_sq) <- #nxh @τ
    {{{ RET #(); th_phase_frag τ π q ∗ dequeue_resources (h + 1) fl nxh (Some h) ∗
                   ∃ i r b, ith_read i r (h + 1) ∗ ⌜ r <= h ⌝ ∗
                               br_lb b ∗
                               (⌜ b < r ⌝ -∗ (ith_rp i rs_canceled ∨ ith_rp i (rs_proc (Some rsp_completed)))) }}}.
  Proof using.
    simpl.
    iIntros (Φ) "([#QAT #INV] & #HTH & PH & CPS & DR) POST".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER & QI & DANGLE & OHV & RHI & RH & DQ)".
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

    iMod (dangle_update _ _ (Some h) with "[$] [$]") as "[DAUTH DFRAG]".

    iAssert (|==> auths (h + 1) t br fl ∗ @me_exact _ q_me_h (h + 1))%I with "[CH AUTHS]" as "UPD".
    { rewrite /auths. iDestruct "AUTHS" as "(AUTH&?&?&?)". iFrame.
      iApply (me_update with "AUTH CH"). lia. }
    iMod "UPD" as "[AUTHS CH]".

    iApply "POST". iFrame.

    iAssert (queue_interp hq (h + 1) t br fl ∗ hn_interp (ph, (vh, nxh)))%I
      with "[Q TAIL DUMMY HEAD BR FL]" as "[QI HNI]".
    { iFrame. rewrite -!bi.sep_assoc.
      iSplit; [done| ].
      iFrame "%".
      pose proof (take_drop_middle _ _ _ HTH) as SPLIT.
      rewrite -SPLIT.
      assert (length (take h hq) = h) as H_LEN. 
      { apply length_take_le. apply lookup_lt_Some in HTH. lia. }
      rewrite drop_app_length'; [| done]. simpl.
      rewrite cons_middle app_assoc.
      rewrite drop_app_length'.
      2: { rewrite length_app /=. lia. }
      iDestruct "Q" as "[$ $]".
      iSplit.
      { iPureIntro. rewrite -(drop_drop _ _ 1) drop_drop_comm.  
        apply is_LL_into_drop; auto. } 
      rewrite -SPLIT in LL.
      rewrite drop_app_length' in LL; [| done].
      simpl in LL. destruct (drop (S h) hq) eqn:REST.
      - subst. simpl. iFrame.   
      - simpl. destruct h0 as [? [??]]. simpl.
        destruct LL as [-> ?]. by iFrame. }

    iDestruct (cancel_rop with "[$]") as "#CNC".
    { red. rewrite Nat.add_1_r. reflexivity. }
    
    iDestruct (take_snapshot with "[$]") as "#SHT".
    iDestruct "SHT" as "(_&_&#BR_LB&_)". 

    rewrite /read_hist_interp. iDestruct "RHI" as "(ROPA & ROP & RHIST & %RH_WF & #OLDS)". 
    rewrite /rop_interp.
    destruct rop as [n| ]. 
    - iDestruct ("ROP" with "[//]") as "(%r & %rp & READ_ & RP & ROP)".      
      destruct RH_WF as (n' & DOM & [? | [=]] & RH_WF); [done| ]. subst n'. 
      iMod (read_hist_wf_bump with "[$] [RP]") as "(%r' & %rp' & RHIST & #READ & %RH_WF' & RP & %READ_BOUND)".
      { eexists. eauto. }
      { rewrite DOM dom_max_set_fold. iFrame. }
      rewrite DOM dom_max_set_fold. 
      iDestruct (ith_read_agree with "READ READ_") as %<-.
      iFrame "READ". iFrame "%". iFrame "BR_LB". 
      rewrite -(bi.sep_True' ( ⌜ _ ⌝ -∗ _ )%I). iApply fupd_frame_l. iSplit.
      { iIntros (LT). iDestruct "ROP" as "[SAFE | [-> _]]".
        2: { iFrame. }
        iDestruct "SAFE" as "[FROM_HEAD | [FROM_DANGLE | FROM_BR]]".
        - iDestruct "FROM_HEAD" as "[-> [-> | (-> & -> & ?)]]".
          + simpl. iFrame. 
          + lia. 
        - iDestruct "FROM_DANGLE" as "[(-> & -> & %X) ?]".
          clear -X. by destruct X. 
        - iDestruct "FROM_BR" as "([-> ->] & ->)". lia. } 

      iClear "HTH CPS".
      iMod ("CLOS" with "[-]") as "_"; [| done].
      iFrame "QI AUTHS OHV HQ RH DAUTH TOK RHIST ROPA". iNext.
      rewrite Nat.add_sub. rewrite HTH /=. 
      
      iSplit.
      { iPureIntro. red. red in ORDER. repeat split; try lia. }
      iSplitL "HNI". 
      { iRight. by iFrame. }
      rewrite DOM dom_max_set_fold in RH_WF'.
      iFrame "%". 
      iSplit.
      2: { iApply old_rps_olds.
           iDestruct (old_rps_olds with "OLDS") as "foo". 
           by rewrite delete_insert_delete. }
      rewrite /rop_interp. iIntros (i_ [=]). subst i_. 

      iFrame "READ_ RP". 
      iDestruct "ROP" as "[[HEAD | [DANGLE | FL]] | CANCEL_WITNESS]".
      + iDestruct "HEAD" as "(-> & [-> | (-> & -> & TOK)])".
        * iRight. simpl. by iFrame "#∗".
        * iLeft. iRight. iLeft. iFrame.
          iPureIntro. split.
          ** split; [lia | done].
          ** simpl. done. 
      + iDestruct "DANGLE" as "((_ & _ & %) & _)". by destruct H.
      + iDestruct "FL"as "([-> ->] & ->)". 
        iLeft. rewrite /safe_read.
        repeat iRight. done.
      + iDestruct "CANCEL_WITNESS" as "(-> & CW)".
        iRight. by iFrame.
    - destruct RH_WF as (n & DOM & [? | [=]] & RH_WF).
      destruct (hist !! n) as [[[??]?] | ] eqn:NTH. 
      2: { apply not_elem_of_dom in NTH. rewrite DOM in NTH.
           rewrite elem_of_set_seq in NTH. lia. }
      iDestruct (big_sepM_lookup with "OLDS") as "RP".
      { simpl. apply NTH. } 
      iDestruct "RP" as "(%rp & RP & %FIN & #LB)".
      iDestruct (ith_rp_hist_compat with "[$] [$]") as %(? & ? & LE').
      rewrite NTH in H0. inversion H0. subst x. simpl in *.

      iDestruct (read_hist_get hist n with "RHIST") as "#READ".
      { rewrite NTH. repeat f_equal. }
      
      iMod (read_hist_wf_bump with "[$] [RP]") as "(%r' & %rp' & RHIST & #READ' & %RH_WF' & RP_ & %READ_BOUND)".
      { eexists. eauto. }
      { rewrite DOM dom_max_set_fold. iFrame "RP". }
      rewrite DOM dom_max_set_fold.
      iDestruct (ith_read_agree with "READ READ'") as %->.
      iFrame "% READ' BR_LB".
      rewrite -(bi.sep_True' ( ⌜ _ ⌝ -∗ _ )%I). iApply fupd_frame_l. iSplit.
      { iIntros (LT). destruct FIN as [-> | [-> | ->]].
        all: try by iFrame.
        iDestruct (br_lb_bound with "[$] [$]") as %?. lia. }

      iMod ("CLOS" with "[-]") as "_"; [| done].
      iFrame "QI AUTHS OHV HQ RH DAUTH TOK RHIST". iNext.
      iExists _. rewrite Nat.add_sub. rewrite HTH /=.
      
      iSplit.
      { iPureIntro. red. red in ORDER. repeat split; try lia. }
      iSplitL "HNI". 
      { iRight. by iFrame. }
      rewrite DOM dom_max_set_fold in RH_WF'.
      destruct RH_WF as (SEQ &  BB). 
      Unshelve. 2: exact None. 
      rewrite bi.sep_assoc.
      iFrame "ROPA". 
      rewrite /rop_interp. iSplit. 
      { iIntros (i_ [=]). }
      iSplitR.
      2: { (* TODO: make a lemma? *)
        rewrite /old_rps. simpl.
        rewrite -insert_delete_insert.         
        rewrite insert_union_singleton_l big_sepM_union.
        2: { apply map_disjoint_dom. rewrite dom_insert_L. set_solver. }
        iSplitL.
        2: { iApply (big_sepM_subseteq with "[$]"). apply delete_subseteq. }
        rewrite big_sepM_singleton. iFrame. iFrame "% #".
        iPureIntro. by apply upd_rp_fin_pres. }

      (* TODO: make a lemma *)
      rewrite /read_hist_wf.
      iPureIntro. 

      exists n. split; [| split; [| split]]. 
    + rewrite dom_insert_L. apply mk_is_Some, elem_of_dom in NTH. set_solver.
    + tauto. 
    + intros ?????. rewrite !lookup_insert_Some.
      intros [(? & ?) | (? & ITH) ] [(? & ?) | (? & JTH) ]; subst; simpl in *; try lia.
      * apply mk_is_Some, elem_of_dom in JTH.
        rewrite DOM elem_of_union elem_of_set_seq elem_of_singleton in JTH. lia.
      * eapply SEQ in H1; eauto. done.
      * eapply SEQ; eauto.
    + intros ??. rewrite lookup_insert_Some.         
      intros [(? & ?) | (? & ITH) ]; subst; simpl; try lia.
      eapply BB in ITH; eauto. simpl in ITH. lia.
  Qed.

  Definition dequeue_fuel := 100.    

  Lemma check_BR_spec l τ π q h fl ph ndh i r b0
    (READ_BOUND: r <= h):
    {{{ queue_inv l ∗
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
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER & QI & DANGLE & OHV & RHI & RH & DQ)".
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

    iDestruct (br_lb_bound with "BR0 AUTHS") as %BR0. 
    iDestruct (take_snapshot with "[$]") as "#SHT".
    iDestruct (hq_auth_get_ith with "HQ") as "#BRTH'".
    { apply BRTH. }
    iFrame "BRTH'". 

    iAssert (queue_interp hq (h + 1) t br fl)%I with "[PQI BR FL]" as "QI".
    { by iFrame. }
    iAssert (br_lb br ∗ ⌜b0 ≤ br⌝)%I as "$".
    { iSplit; [| done].
      iDestruct "SHT" as "(?&?&?&?)". done. }

    simpl.
    destruct (decide (pbr = ph)) as [-> | NEQ].
    -
      iFrame. 
      iMod ("CLOS" with "[-]") as "_".
      { iFrame "#∗ %". iNext.
        rewrite Nat.add_sub HTH /=.
        iRight. by iFrame. }
      iModIntro. by iLeft.
    - rewrite /read_hist_interp. iDestruct "RHI" as "(ROPA & ROP & RHIST & %RH_WF & #OLDS)".  
      iDestruct (ith_read_hist_compat with "[$] [$]") as %(b & p & READ & INCR_BOUND). 
      iMod (dangle_update _ _ None with "[$] [$]") as "[DAUTH DFRAG]".
      iFrame.      
      iApply fupd_or. iRight. iFrame "HNI".
      rewrite -(bi.sep_True' ⌜ _ ≠ _ ⌝%I). iApply fupd_frame_l. iSplit; [done| ].
      iMod ("CLOS" with "[-]") as "_"; [| done]. 

      rewrite /rop_interp.
      destruct rop.
      2: { iFrame "#∗ %". iNext. iSplitR.
           { by iLeft. }
           rewrite /rop_interp. by iIntros (??). }
      
      iDestruct ("ROP" with "[//]") as "(%r_ & %rp & READ_ & RP & ROP)".
      iDestruct (ith_read_hist_compat with "[$] READ_") as %(?&? & READ' & _). 

      iFrame. iFrame "OLDS".
      iNext. iFrame (RH_WF ORDER). iSplitR.
      { by iLeft. }
      rewrite /rop_interp.
      iIntros (i' [=]). subst n.
      iDestruct "ROP" as "[SAFE | $]".
      2: { iFrame "#∗". }

      destruct (decide (i' = i)). 
      { subst. rewrite {1}/safe_read. rewrite Nat.add_sub.
        iFrame "READ_". 
        iDestruct "SAFE" as "[FROM_HEAD | [FROM_DANGLE | FROM_BR]]".
        - iFrame.
        - iDestruct "FROM_DANGLE" as "[(-> & -> & _) ?]".
          congruence.
        - iFrame. }

      assert (i < i') as NEW.
      { red in RH_WF. destruct RH_WF as (n' & DOM & [? | [=]] & RH_WF); [done| ].
        subst i'.
        apply mk_is_Some, elem_of_dom in READ. rewrite DOM elem_of_set_seq in READ.
        lia. }
      clear n.
      
      assert (h + 1 <= r_) as READ'_BOUND.
      { red in RH_WF. destruct RH_WF as (n' & DOM & [? | [=]] & RH_WF); [done| ].
        subst. 
        apply proj1 in RH_WF. eapply RH_WF in NEW; eauto. simpl in NEW. lia. }
      iFrame "READ_".
      rewrite {1}/safe_read.
      iDestruct "SAFE" as "[FROM_HEAD | [FROM_DANGLE | FROM_BR]]".
      + iFrame.
      + iDestruct "FROM_DANGLE" as "[(-> & -> & _) ?]". lia.
      + iFrame.
  Qed.

  Lemma read_FL_spec τ π l h q fl nd od:
  {{{ queue_inv l ∗ dequeue_resources h fl nd od ∗
      cp π d ∗ th_phase_frag τ π q }}}
    ! #(FreeLater q_sq) @τ
  {{{ (pfl: loc), RET (#pfl);
      ∃ ndfl, ith_node fl (pfl, ndfl) ∗ 
      dequeue_resources h fl nd od ∗ th_phase_frag τ π q }}}.
  Proof using.
    iIntros (Φ) "([#QAT #INV] & DR & CPS & PH) POST".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER & QI & DANGLE & OHV & RHI & RH & DQ)".
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
    {{{ queue_inv l ∗
        ith_node h (ph, ndh) ∗
        dequeue_resources (h + 1) fl ndh.2 (Some h) ∗ 
        th_phase_frag τ π q ∗ cp_mul π d (get_loc_fuel + get_loc_fuel + get_loc_fuel) ∗
        ith_read i r (h + 1) ∗
        br_lb b ∗ (⌜ b < r ⌝ -∗ (ith_rp i rs_canceled ∨ ith_rp i (rs_proc (Some rsp_completed))))
    }}}
      get_to_free q_sq #ph @ τ
    {{{ (to_free: loc), RET #to_free;
        ∃ hn fl', hn_interp (to_free, hn) ∗ th_phase_frag τ π q ∗
                    dequeue_resources (h + 1) fl' ndh.2 None }}}.
  Proof using.
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
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER & QI & DANGLE & OHV & RHI & RH & DQ)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-]. 
    iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->.

    iClear "INV QAT".

    (* TODO: split into lemmas *)
    iDestruct (hq_auth_lookup with "[$] HTH") as %HTH.
    iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
    { iIntros (->). red in ORDER. lia. }

    iPoseProof (queue_interp_dangle_neq_pfl' _ _ _ _ _ ph with "QI [DANGLE]") as "#PFL_NEQ_D".
    { by rewrite Nat.add_sub. }

    rewrite /dangle_interp. iDestruct "DANGLE" as "(DAUTH & [% | (_ & HNI)])"; [done| ].
    rewrite Nat.add_sub HTH /=. 
    rewrite /dequeue_resources. iDestruct "DR" as "(CH & CFL & HEAD' & DFRAG)".

    
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
    iDestruct "BR" as "(%nbr & %BRTH & BR)".    
    iDestruct (br_lb_bound with "BR1 AUTHS") as %BR1. 

    subst pbr. 
    destruct nbr as [pbr nbr].

    (* iCombine "HEAD HEAD'" as "HEAD".  *)
    iApply sswp_MU_wp; [done| ].

    iDestruct "FL" as "(%ndfl_ & %FLTH & FL & HNI_FL)".
    iDestruct (hq_auth_lookup with "[$] FLTH") as %FLTH_.
    rewrite FLTH in FLTH_. inversion FLTH_. subst ndfl_. clear FLTH_. 
    iApply (wp_store with "FL"). iIntros "!> FL".
    MU_by_burn_cp. iApply wp_value.

    iMod (dangle_update _ _ None with "[$] [$]") as "[DAUTH DFRAG]".
    iAssert (|==> auths (h + 1) t br h ∗ @me_exact _ q_me_fl h)%I with "[CFL AUTHS]" as "UPD".
    { rewrite /auths. iDestruct "AUTHS" as "(?&?&?&A)". iFrame.
      iApply (me_update with "A CFL"). red in ORDER. lia. }
    iMod "UPD" as "[AUTHS CFL]".

    iDestruct (br_lb_bound with "BR0 [$]") as %BR0. 
    iAssert (queue_interp hq (h + 1) t br h)%I
      with "[PQI BR FL HNI]" as "QI".
    { iFrame. iSplit; [done| ].
      iFrame "%". iFrame. }

    rewrite /read_hist_interp. iDestruct "RHI" as "(ROPA & ROP & RHIST & %RH_WF & #OLDS)". 
    rewrite /rop_interp.
    destruct rop. 
    - iDestruct ("ROP" with "[//]") as "(%r_ & %rp & READ_ & RP & ROP)".
      iDestruct (ith_read_hist_compat with "[$] READ_") as %(?&? & READ' & _). 
      iDestruct (ith_read_hist_compat with "[$] READ") as %(?&? & READ & BB).
      iDestruct (hq_auth_lookup with "[$] BRTH1") as %BRTH1.
      
      iAssert (dequeue_resources (h + 1) h ndh.2 None)%I with "[CH CFL HEAD' DFRAG]" as "DR".
      { iFrame. }

      iMod ("CLOS" with "[-POST CPS PH DR HNI_FL]") as "_".
      { iFrame. iNext. iFrame "OLDS". iFrame (RH_WF).
        iSplit. 
        { rewrite /hq_state_wf. iPureIntro. red in ORDER. lia. }
        iSplitR.
        { by iLeft. }        
        rewrite /rop_interp.
        iIntros (i' [=]). subst n.
        iDestruct "ROP" as "[SAFE | $]".
        2: { iFrame. }
        iFrame "READ_".
          
        destruct (decide (i' = i)). 
        { subst. rewrite {1}/safe_read. rewrite Nat.add_sub.
          iDestruct "SAFE" as "[FROM_HEAD | [FROM_DANGLE | FROM_BR]]".
          - iFrame.
          - iDestruct "FROM_DANGLE" as "[(-> & -> & _) ->]".
            iFrame "RP". 
            iLeft. rewrite /safe_read. rewrite Nat.add_sub.
            do 2 iRight. by iFrame. 
          - iDestruct "FROM_BR" as "([-> ->] & ->)". 
            rewrite READ in READ'. inversion READ'. subst r x1 x2.
            apply Nat.le_lteq in BR0 as [BR0 | ->].
            { iSpecialize ("NO_FL" with "[//]"). iExFalso.
              iAssert (∃ rp', ith_rp i rp' ∗ ⌜ rp' = rs_canceled \/ rp' = (rs_proc (Some rsp_completed))⌝)%I as "(%rp' & RP' & %RP')".
              { iDestruct "NO_FL" as "[$|$]"; set_solver. }
              iDestruct (ith_rp_le with "RP RP'") as %CM.
              exfalso. clear -RP' CM.
              inversion CM; destruct RP' as [-> | ->]; try done.
              subst. inversion RSP. by subst. }
            rename x into bi.
            red in RH_WF.
            destruct RH_WF as (n' & DOM & [? | [=]] & SEQ & BB'); [done| ].
            subst n'.
            pose proof READ as EQ%BB'. simpl in EQ.
            assert (bi = h + 1) as -> by lia.  clear BB EQ.
            assert (b1 = fl) as -> by lia.
            rewrite BRTH in BRTH1. inversion BRTH1. subst pbr ndbr1.
            iDestruct ("PFL_NEQ_D" with "[] []") as "?".
            { eauto. }
            { eauto. }
            done. }
          
        assert (i < i') as NEW.
        { red in RH_WF. destruct RH_WF as (n' & DOM & [? | [=]] & RH_WF); [done| ].
          subst i'.
          apply mk_is_Some, elem_of_dom in READ. rewrite DOM elem_of_set_seq in READ.
          lia. }
        clear n.

        assert (h + 1 <= r_) as READ'_BOUND.
        { red in RH_WF. destruct RH_WF as (n' & DOM & [? | [=]] & RH_WF); [done| ].
          apply proj1 in RH_WF. eapply RH_WF in NEW; eauto. simpl in NEW. lia. }
        rewrite {1}/safe_read.
        iDestruct "SAFE" as "[FROM_HEAD | [FROM_DANGLE | FROM_BR]]".
        + iFrame.
        + iDestruct "FROM_DANGLE" as "[(-> & -> & _) ?]". lia.
        + iFrame.
          iDestruct "FROM_BR" as "([% %] & ?)". subst.
          red in ORDER. lia. }
      iModIntro. wp_bind (Rec _ _ _)%E. pure_steps.
      iApply "POST". iFrame. 
    - 
      iAssert (dequeue_resources (h + 1) h ndh.2 None)%I with "[CH CFL HEAD' DFRAG]" as "DR".
      { iFrame. }

      iMod ("CLOS" with "[-POST CPS PH DR HNI_FL]") as "_".
      { iFrame. iNext. iFrame "OLDS". iFrame (RH_WF). iSplit.
        { rewrite /hq_state_wf. iPureIntro. red in ORDER. lia. }
        iSplitR.
        { by iLeft. }
        rewrite /rop_interp. by iIntros (??). }

      iModIntro. wp_bind (Rec _ _ _)%E. pure_steps.
      iApply "POST". iFrame. 
  Qed.

  Lemma free_el_spec τ π q ptr nd:
    {{{ th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel ∗ 
        hn_interp (ptr, nd) }}}
      free_el #ptr @ τ
    {{{ v, RET v; th_phase_frag τ π q }}}.
  Proof using. Admitted. 
  
  Lemma dequeue_spec l (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ queue_inv l ∗ dequeue_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d dequeue_fuel }}}
      dequeue q_sq l @ τ
    {{{ (v: val), RET v; th_phase_frag τ π q ∗ dequeue_token }}}.
  Proof using.
    simpl. iIntros (Φ) "([#QAT #INV] & TOK & PH & CPS) POST".
    rewrite /dequeue. destruct q_sq eqn:Q_SQ.
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
    wp_bind (Rec _ _ _)%E. pure_steps.

    destruct ndh as [vh nxh]. simpl.
    wp_bind (_ <- _)%E.
    replace OldHeadVal with (simple_queue.OldHeadVal q_sq) by (by rewrite Q_SQ).
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].     
    iApply (update_ohv_spec with "[$QAT $PH $CPS' $INV]").
    iIntros "!> PH".
    wp_bind (Rec _ _ _)%E. pure_steps.

    split_cps "CPS" get_loc_fuel; [cbv; lia| ].
    iApply (get_head_next_spec with "[-POST CPS]").
    { iFrame "#∗". }
    iIntros "!> [PH DR]". simpl.

    wp_bind (_ <- _)%E.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].
    iApply (dequeue_upd_head_spec with "[$QAT $CPS' $PH $INV $HTH $DR]").
    iIntros "!> (PH & DR & (%i & %r & %b & #ITHR & %BR & #TOKS))".

    wp_bind (Rec _ _ _)%E. do 3 pure_step_cases.
    fold (get_to_free (SQ Head Tail BeingRead FreeLater OldHeadVal)).
    rewrite -Q_SQ. 
    wp_bind (get_to_free _ _)%E.         
    split_cps "CPS" (3 * get_loc_fuel); [cbv; lia| ].
    iApply (get_to_free_spec with "[-POST CPS]").
    { apply BR. }
    { iFrame "#∗". }
    
    iIntros "!> %to_free (%hfr & %fl' & HNFR & PH & DR)".
    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (free_el _)%E.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].
    iApply (free_el_spec with "[CPS' PH HNFR]").
    { iFrame. }
    iIntros "!> %v PH".

    wp_bind (Rec _ _ _)%E. do 2 pure_step_cases. 
    iClear "TOKS ITHR HTH". 
    clear dependent r t hfr to_free br ph b. 

    iApply sswp_MU_wp_fupd; [done| ]. 
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER & QI & DANGLE & OHV & RHI & RH & DQ)".
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

    
End Dequeue.
