From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth gmap.
From fairness Require Import utils.
From lawyer.nonblocking.examples.queue Require Import simple_queue_utils simple_queue.
From heap_lang Require Import heap_lang_defs lang notation.

Close Scope Z.


Section ReadHeadViewshifts.
  Context {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}.  
  Context {QL: QueueG Σ}.
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}.

  Context (PE: val -> iProp Σ). 

  (* TODO: move, remove duplicates *)
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

  Lemma read_hist_alloc (hist: read_hist) h
    (RH_WF: read_hist_wf hist None h)
    (n' := set_fold max 0 (dom hist) + 1):
    read_hist_auth hist ==∗
    let hist' := <[ n' := ((h, h), rs_init) ]> hist in
    read_hist_auth hist' ∗ ith_read n' h h ∗ ⌜ read_hist_wf hist' (Some n') h ⌝ ∗
    ith_rp n' rs_init.
  Proof using.
    simpl. iIntros "AUTH".
    destruct RH_WF as (n & DOM & ROP & SEQ & BB).
    clear ROP.

    assert (n' = S n) as ->.
    { subst n'. rewrite DOM dom_max_set_fold. lia. }    
    
    iMod (read_hist_alloc hist (S n) h h rs_init with "AUTH") as "(AUTH & #ITH & RP)".
    { rewrite DOM. rewrite elem_of_set_seq. lia. }
    iFrame "#∗". 
    iPureIntro. red. 
        
    exists (S n). split; [| split; [| split]]. 
    - rewrite dom_insert_L. rewrite DOM.
      rewrite !set_seq_S_end_union_L. set_solver. 
    - tauto.
    - intros ?????. rewrite !lookup_insert_Some.
      intros [(? & ?) | (? & ITH) ] [(? & ?) | (? & JTH) ]; subst; simpl in *; try lia.
      + apply mk_is_Some, elem_of_dom in JTH.
        rewrite DOM elem_of_union elem_of_set_seq elem_of_singleton in JTH. lia.
      + eapply BB; eauto. 
      + eapply SEQ in H; eauto; try done.
    - intros ??. rewrite lookup_insert_Some.         
      intros [(? & ?) | (? & ITH) ]; subst; simpl; try lia.
      eapply BB in ITH; eauto. 
  Qed.
    
  Lemma start_rop hist rop_ h br pt fl od t:
  read_hist_interp hist rop_ h br fl od -∗ read_head_resources t br pt None ==∗
  ∃ i hist', read_hist_interp hist' (Some i) h br fl od ∗ read_head_resources t br pt (Some i) ∗ 
              ith_read i h h.
  Proof using.
    iIntros "ROP RH".
    iDestruct (read_head_resources_rop_interp_agree with "[$] [$]") as %<-.
    rewrite {1}/read_hist_interp {1}/read_head_resources.
    iDestruct "ROP" as "(ROPA & ROP & RHIST & %RH_WF & #OLDS)".
    iDestruct "RH" as "(TLA & BRA & TAIL & ROPF)".
    rewrite /rop_interp. iClear "ROP".

    iMod (read_hist_alloc with "[$]") as "(AUTH & #READ & %RH_WF' & RP)"; [done| ].
    red in RH_WF.
    destruct RH_WF as (n & DOM & ROP & SEQ & BB).
    assert (set_fold Init.Nat.max 0 (dom hist) + 1 = S n) as EQ. 
    { rewrite DOM dom_max_set_fold. lia. }
    rewrite EQ. rewrite EQ in RH_WF'.

    iMod (rop_update _ _ (Some (S n)) with "[$] [$]") as "(ROPA & ROPF)". 
    iFrame "#∗".
    iModIntro. iSplitL.
    2: { iSplit; [done| ].
         iApply old_rps_olds. rewrite delete_insert; [done| ].
         apply not_elem_of_dom. rewrite DOM. rewrite elem_of_set_seq. lia. }
    rewrite /rop_interp. iIntros (? [=<-]).
    iFrame "RP". iExists _. iSplit.
    { iApply (ith_included with "READ"). lia. }
    iLeft. rewrite /safe_read. iLeft. iSplit; try done.
    by iLeft.
  Qed.

  Definition h_lb (b: nat) := @me_lb _ q_me_h b.

  Lemma h_lb_bound b h t br fl:
    h_lb b -∗ auths h t br fl -∗ ⌜ b <= h ⌝.
  Proof using.
    iIntros "LB (H&?&?&?)".
    iApply (me_auth_lb with "H LB").
  Qed.  

  Lemma old_rps_extend hist n r rp
    (NTH: exists b, hist !! n = Some ((r, b), rp)):
    old_rps hist (Some n) -∗
    (ith_rp n rp ∗ ⌜rs_fin rp⌝ ∗ (br_lb r ∨ ⌜rp = rs_aborted ∨ rp = rs_canceled⌝)) -∗
    old_rps hist None.
  Proof using.
    iIntros "OLDS (RP & %FIN & #ADD)".
    rewrite /old_rps. simpl.
    rewrite {2}(map_split hist n).
    destruct NTH as (b & NTH). rewrite NTH /=.  
    rewrite big_sepM_union.
    2: { destruct lookup; simpl; apply map_disjoint_dom; set_solver. }
    iFrame.     
    rewrite big_sepM_singleton.
    iFrame "#∗ %".
  Qed.

  Lemma finish_read_op t br pt i hist h fl od (* rp rp' *) rp
    (* (STEP: rs_step rp rp') *)
    (* (FIN: rs_fin rp') *)
    (RP: rp = rs_canceled \/ rp = rs_proc None)
    :
    read_head_resources t br pt (Some i) -∗
    read_hist_interp hist (Some i) h br fl od -∗
    br_lb br -∗
    (* ith_rp i (rs_proc None) *)
    ith_rp i rp
 ==∗
  ∃ hist', read_head_resources t br pt None ∗ read_hist_interp hist' None h br fl od ∗ (⌜ rs_compat (rs_proc None) rp⌝ -∗ rop_token).
  Proof using.
    iIntros "RH ROP #BR RP0".
    rewrite {1}/read_hist_interp {1}/read_head_resources.
    iDestruct "ROP" as "(ROPA & ROP & RHIST & %RH_WF & #OLDS)".
    iDestruct "RH" as "(TLA & BRA & TAIL & ROPF)".
    rewrite /rop_interp. iDestruct ("ROP" with "[//]") as "(%r & %rp_ & READ_ & RP' & ROP)".
    iDestruct (ith_rp_le with "RP' RP0") as %CM.

    iMod (rop_update _ _ None with "[$] [$]") as "(ROPA & ROPF)".
    iAssert (read_head_resources t br pt None)%I with "[ROPF TAIL TLA BRA]" as "$".
    { iFrame. }

    destruct RH_WF as (n & DOM & ROP & SEQ & BB).
    iDestruct (ith_read_hist_compat with "[$] [$]") as %(?&rpa&NTH&_). 
    iDestruct (ith_rp_hist_compat with "[$] [$]") as %(xx&NTH_&RS_LE).
    rewrite NTH in NTH_. inversion NTH_. subst xx. simpl in *. clear NTH_. 

    iDestruct "ROP" as "[SAFE | [-> #CW]]".
    2: { iModIntro. iFrame "RHIST". iFrame "#∗".
         inversion CM. subst.
         iSplitL.
         2: { iIntros (X). inversion X. }
         
         iSplitR.
         { rewrite /rop_interp. by iIntros "% %". }
         iSplit.
         { iPureIntro. red. eexists. eauto. }
         
         destruct ROP as [[=] | [=]]. subst.
         iApply (old_rps_extend with "[$]").
         { eauto. }
         inversion RS_LE; subst. iFrame "#∗".
         iSplit; [iPureIntro; red; tauto| ].
         iRight. set_solver. }

    rewrite /safe_read.
    (* TODO: refactor *)
    iDestruct "SAFE" as "[FROM_HEAD | GOING]".
    2: { iFrame "RHIST". iFrame "#∗". iModIntro.
         iAssert (⌜ rp_ = rs_proc (Some rsp_protected)⌝ ∗ rop_token ∗ ⌜ r = br ⌝)%I with "[GOING]" as "(-> & RTOK & ->)".
         { iDestruct "GOING" as "[((? & ? & ?) & -> & TOK) | ((? & ?) & ? & TOK)]"; by iFrame. }
         inversion RS_LE. subst.
         iSplitR "RTOK".
         2: { by iFrame. } 

         iSplitR.
         { rewrite /rop_interp. by iIntros "% %". }
         iSplit.
         { iPureIntro. red. eexists. eauto. }
         destruct ROP as [[=] | [=]]. subst.
         iApply (old_rps_extend with "[$]").
         { eauto. }
         iFrame "#∗".
         iPureIntro. red. tauto. }
         
    iDestruct "FROM_HEAD" as "(-> & [-> | (<- & -> & RTOK)])".
    { inversion CM. }
    inversion RS_LE. subst.

    iDestruct (read_hist_update' with "RHIST RP'") as "X".
    { apply rs_going_protected. apply rsp_going_completed. }
    { apply NTH. }
    erewrite Nat.max_id. rewrite decide_False; [| done].
    iMod "X" as "(RHIST & #READ' & #RP)".     
    
    iExists _. 
    iSplitR "RTOK".
    2: { by iFrame. }
    iFrame . iModIntro. 
    iSplitR.
    { rewrite /rop_interp. by iIntros (? [=]). }

    iSplit.
    2: { iApply (old_rps_extend _ i).
         { eexists. rewrite (lookup_insert hist). reflexivity. }
         { iApply old_rps_olds.
           rewrite old_rps_olds.
           replace (delete i (insert _ _ _ )) with (delete i hist); [done| ].
           by rewrite delete_insert_delete. }
         iFrame "BR RP".
         iPureIntro. red. tauto. }

    (* TODO: find duplicates, make a lemma *)
    iPureIntro.
    red.
    exists n. split; [| split; [| split]]. 
    - rewrite dom_insert_L. rewrite DOM.
      apply mk_is_Some, elem_of_dom in NTH. set_solver. 
    - tauto.
    - intros ?????. rewrite !lookup_insert_Some.
      intros [(? & ?) | (? & ITH) ] [(? & ?) | (? & JTH) ]; subst; simpl in *; try lia.
      + eapply SEQ in H; eauto. done. 
      + eapply BB; eauto. 
      + eapply SEQ in H; eauto; try done.
    - intros ??. rewrite lookup_insert_Some.         
      intros [(? & ?) | (? & ITH) ]; subst; simpl; try lia.
      + eapply BB in NTH; eauto.
      + eapply BB in NTH; eauto.  
  Qed.

  Definition disj_range (h t: nat): iProp Σ :=
    let range := set_seq h (t - h): gset nat in
    (* ([∗ set] i ∈ range, ∃ nd, ith_node i nd) ∗ *)
    (∀ i j ndi ndj, ⌜ i ≠ j /\ i ∈ range /\ j ∈ range ⌝ -∗
                      □ (ith_node i ndi -∗ ith_node j ndj -∗ ⌜ ndi.1 ≠ ndj.1 ⌝)).

  Lemma phys_queue_interp_disj_impl' (pq: HistQueue) i j p
    (LT : i < j)
    (ITH : exists nd, pq !! i = Some (p, nd))
    (JTH : exists nd, pq !! j = Some (p, nd)):
  ([∗ list] nd ∈ pq, hn_interp nd) -∗ False.
  Proof using.
    destruct ITH as [? ITH], JTH as [? JTH].
    pose proof JTH as JJ%mk_is_Some%lookup_lt_is_Some.
    apply Nat.lt_exists_pred in LT as (k & -> & LE).
    apply Nat.lt_exists_pred in JJ as (t & EQ & LE').
    erewrite <- (take_drop_middle _ (S k)); eauto.  
    erewrite <- (take_drop_middle (take _ _) i).
    2: { rewrite lookup_take; [| lia]. eauto. }
    repeat rewrite big_sepL_app. simpl.
    iIntros "((?&X&?) & Y & ?)".
    by iDestruct (hn_interp_ptr_excl with "X Y") as %?.
  Qed.

  (* TODO: move *)
  Lemma ith_node_agree i nd1 nd2:
    ith_node i nd1 -∗ ith_node i nd2 -∗ ⌜ nd2 = nd1 ⌝.
  Proof using.
    rewrite bi.wand_curry -!own_op.
    iIntros "X". iDestruct (own_valid with "[$]") as %V.
    rewrite -auth_frag_op singleton_op in V.
    rewrite auth_frag_valid in V. apply singleton_valid in V.
    by apply to_agree_op_inv_L in V.
  Qed.

  Lemma phys_queue_interp_disj_impl (pq: HistQueue):
    phys_queue_interp pq -∗
    ⌜ forall i j ndi ndj, i ≠ j -> pq !! i = Some ndi -> pq !! j = Some ndj -> ndi.1 ≠ ndj.1 ⌝.
  Proof using.
    rewrite /phys_queue_interp. iIntros "(Q & (%pt & TAIL & DUMMY & %LL & HEAD))".
    iIntros (i j [??] [??] NEQ ITH JTH EQ).
    simpl in EQ. subst.
    apply not_eq in NEQ as [?|?].
    - iApply (phys_queue_interp_disj_impl' pq i j); eauto.
    - iApply (phys_queue_interp_disj_impl' pq j i); eauto.
  Qed.

  Lemma phys_queue_interp_disj (hq: HistQueue) h:
    phys_queue_interp (drop h hq) -∗ hq_auth hq  -∗ disj_range h (length hq).
  Proof using.
    iIntros "PQI AUTH". 
    iDestruct (phys_queue_interp_disj_impl with "PQI") as %DISJ. 
    rewrite /phys_queue_interp. iDestruct "PQI" as "(Q & (%pt & TAIL & DUMMY & %LL & HEAD))".
    iIntros (i j [??] [??] (NEQ & II & JJ)).
    simpl.
    apply elem_of_set_seq in II, JJ.
    destruct (decide (h <= length hq)); [| lia].
    pose proof II as ?. pose proof JJ as ?. 
    rewrite -Nat.le_add_sub in II, JJ; try done.
    destruct II as [HI ITH], JJ as [HJ JTH].
    apply lookup_lt_is_Some in ITH as [? ITH], JTH as [? JTH].
    iDestruct (hq_auth_get_ith with "AUTH") as "#ITH"; [apply ITH| ].
    iDestruct (hq_auth_get_ith with "AUTH") as "#JTH"; [apply JTH| ].
    iModIntro. iIntros "ITH' JTH'".
    iDestruct (ith_node_agree with "ITH' ITH") as %->. 
    iDestruct (ith_node_agree with "JTH' JTH") as %->.
    iIntros (<-).
    apply Nat.le_sum in HI as [u ->], HJ as [v ->].
    assert (u ≠ v) as NEQ' by lia. 
    eapply DISJ in NEQ'.
    2, 3: rewrite lookup_drop; eauto.
    done.
  Qed.  

  (* TODO: move *)
  Lemma ith_rp_get_rs_p0 i rs
    (LE: rs_le (rs_proc None) rs):
    ith_rp i rs -∗ ith_rp i (rs_proc None).
  Proof using.
    rewrite /ith_rp. iApply own_mono.
    apply auth_frag_mono. apply singleton_included_mono.
    apply pair_included. split; [done| ].
    by apply rs_le_incl.
  Qed.

  Lemma bump_BR_vs t br pt h ndh i ph
    (BRH: br <= h):
    queue_inv PE -∗ read_head_resources t br pt (Some i) -∗
    rop_token -∗ ith_node h (ph, ndh) -∗ ith_read i h 0 -∗
    |={⊤, ⊤ ∖ ↑queue_ns}=> ∃ (pbr0: loc), ▷ BeingRead ↦ #pbr0 ∗
        ▷ (BeingRead ↦ #ph -∗ |={⊤ ∖ ↑queue_ns, ⊤}=> read_head_resources t h pt (Some i) ∗ rop_token).
  Proof using. 
    iIntros "#INV RH RTOK #HTH #READ".

    iInv "INV" as "(%hq & %h' & %t_ & %br_ & %fl & %rop_ & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH' & >DQ & EI)".
    iDestruct "RH'" as "[(% & RH' & RTOK') | TOK']".
    { by iDestruct (read_head_resources_excl with "RH RH'") as "?". }
    iDestruct (read_head_resources_auth_agree with "[$] [$]") as %[<- <-].
    iDestruct (read_head_resources_rop_interp_agree with "[$] [$]") as %<-.

    rewrite /read_hist_interp. iDestruct "RHI" as "(ROPA & ROP & RHIST & %RH_WF & #OLDS)".
    rewrite /rop_interp. iDestruct ("ROP" with "[//]") as "(%r & %rp & READ_ & RP & ROP)".
    iDestruct (ith_read_agree with "READ READ_") as %->.
    iDestruct (ith_read_hist_compat with "[$] [$]") as %(?&?&ITH&_).

    iAssert (|==> auths h' t h fl ∗ read_head_resources t h pt (Some i))%I with "[AUTHS RH]" as ">[AUTHS RH]".
    { iDestruct "AUTHS" as "($&$&BR&$)".
      rewrite /read_head_resources. iDestruct "RH" as "($&BR'&$)".
      by iApply (me_update with "BR [$]"). }

    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
    iDestruct "BR" as "(%nbr & %BRTH & BR)".
    iFrame "BR". iIntros "!> !> BR". 

    iDestruct (hq_auth_lookup with "[$] [$]") as %HTH.
    iAssert (|==> queue_interp hq h' t h fl)%I with "[PQI BR FL]" as ">QI".
    { iFrame. iModIntro. iSplit; [done| ].
      iExists (_, _). iFrame. eauto. }

    iAssert (rop_interp (Some i) h' h fl od ∗ rop_token)%I with "[ROP RP RTOK]" as "[ROP RTOK]".
    { iDestruct "ROP" as "[SAFE | CANC]".
      2: { iFrame "RTOK". rewrite /rop_interp.
           iIntros (? [=<-]). iFrame "#∗". }
      rewrite /safe_read.
      iDestruct "SAFE" as "[FROM_HEAD | [FROM_DANGLE | FROM_BR]]".
      - iDestruct "FROM_HEAD" as "[-> [-> | (-> & -> & RTOK')]]".
        + iFrame. iIntros (? [=<-]). iFrame "#∗".
          iLeft. rewrite /safe_read. iLeft. iSplit; [done| ]. by iLeft.
        + by iDestruct (rop_token_excl with "[$] [$]") as "?".
      - iDestruct "FROM_DANGLE" as "((-> & -> & %X) & ? & RTOK')".
        by iDestruct (rop_token_excl with "[$] [$]") as "?".
      - iDestruct "FROM_BR" as "([-> ->] & -> & RTOK')".
        by iDestruct (rop_token_excl with "[$] [$]") as "?". }

    iAssert (read_hist_interp hist (Some i) h' h fl od)%I with "[ROPA ROP RHIST]" as "RHI".
    { iFrame "#∗". done. }

    iFrame.
    iMod ("CLOS" with "[-]") as "_"; [| done].
    iFrame. iPureIntro.
    red. split; [| apply ORDER].
    red in RH_WF. destruct RH_WF as (n & DOM & ROP & SEQ & BB).
    eapply BB in ITH. simpl in ITH. lia.
  Qed.

  Context {PERS_PE: forall v, Persistent (PE v)}. 

  Lemma start_read_vs:
    queue_inv PE -∗ read_head_token -∗
    |={⊤, ⊤ ∖ ↑queue_ns}=> ∃ (ph: loc), ▷ Head ↦{1 / 2} #ph ∗ ▷ (Head ↦{1 / 2} #ph -∗ |={⊤ ∖ ↑queue_ns, ⊤}=>
        rop_token ∗ ∃ t br pt rop, read_head_resources t br pt rop ∗
           (⌜ pt = ph /\ rop = None ⌝ ∨ 
            ∃ i h ndh, ⌜ pt ≠ ph /\ rop = Some i ⌝ ∗ ith_node h (ph, ndh) ∗
                        ith_read i h 0 ∗ ⌜ br <= h ⌝ ∗ disj_range h t ∗ PE ndh.1)).
  Proof using PERS_PE.
    iIntros "#INV TOK".

    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & #EI)".
    iModIntro. 
    
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph & %pt & HEAD & TAIL & #HT & CLOS')".
    iFrame "HEAD". iIntros "!> HEAD". 
    iDestruct "RH" as "[(%pt_ & RH & RTOK) | TOK']".
    2: { by iDestruct (read_head_token_excl with "[$] [$]") as "?". }
    iDestruct (read_head_res_Tail_agree with "RH [$]") as %EQ.
    inversion EQ. subst pt_. clear EQ. 
      
    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".

    iDestruct "HT" as "[(%GE & <-) | ((%LT & %NEQ) & (%ndh & #HTH))]".
    - iFrame.
      iMod ("CLOS" with "[-]") as "_".
      { iFrame. by iFrame "EI". }      
      set_solver.
    - iMod (start_rop with "RHI RH") as "(%i & %hist' & RHI & RH & #ITH)". 
      iFrame.
      iAssert (disj_range h t) with "[QI HQ]" as "#DISJ".
      { rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
        subst. iApply (phys_queue_interp_disj with "[$] [$]"). }
      iFrame "DISJ".
      iDestruct (hq_auth_lookup with "[$] [$]") as %HTH. 
      iDestruct (queue_elems_interp_get with "EI") as "PEv"; eauto. 
      iMod ("CLOS" with "[-]") as "_".
      { iFrame. by iFrame "EI". }
      iRight. iFrame "PEv". 
      iFrame "#∗". iModIntro.
      iExists _. 
      iSplit; [done| ]. 
      iSplit.
      2: { red in ORDER. iPureIntro. lia. }
      iApply (ith_included with "ITH"). lia.
  Qed.

  Lemma read_tail_exact_vs t br pt rop:
    queue_inv PE -∗ read_head_resources t br pt rop -∗
    |={⊤, ⊤ ∖ ↑queue_ns}=> ▷ Tail ↦{1 / 2} #pt ∗ 
        ▷ (Tail ↦{1 / 2} #pt -∗ |={⊤ ∖ ↑queue_ns, ⊤}=> read_head_resources t br pt rop).
  Proof using.
    simpl. iIntros "#INV RH".

    iInv "INV" as "(%hq & %h & %t_ & %br_ & %fl & %rop_ & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH' & >DQ & EI)".
    iModIntro.
    
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph & %pt_ & HEAD & TAIL & #HT & CLOS')".    
    iDestruct (read_head_res_Tail_agree with "RH [$]") as %EQ.
    inversion EQ. subst pt_. clear EQ.
    iFrame "TAIL". iIntros "!> TAIL". 
    
    iDestruct "RH'" as "[(% & RH' & RTOK) | TOK']".
    { by iDestruct (read_head_resources_excl with "RH RH'") as "?". }
      
    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".
    iFrame.
    iMod ("CLOS" with "[-]") as "_"; by iFrame.
  Qed.

  Lemma read_ohv_vs:
    queue_inv PE -∗ 
    |={⊤, ⊤ ∖ ↑queue_ns}=> ∃ v, ▷ OldHeadVal ↦ v ∗ 
        ▷ (OldHeadVal ↦ v -∗ |={⊤ ∖ ↑queue_ns, ⊤}=> PE v).
  Proof using PERS_PE.
    iIntros "#INV".
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iModIntro. 
    iDestruct "OHV" as "(% & OHV & #PEv)".
    iFrame "OHV". iIntros "!> OHV". 
    iMod ("CLOS" with "[-]") as "_". 
    { iFrame. by iFrame "PEv". }
    by iFrame.
  Qed. 

  Lemma get_op_node_val_vs h ph ndh i t pt:
    queue_inv PE -∗ ith_node h (ph, ndh) -∗ ith_read i h 0 -∗
    ith_rp i (rs_proc None) -∗ read_head_resources t h pt (Some i) -∗ 
      |={⊤, ⊤ ∖ ↑queue_ns}=> ∃ v, ▷ ph ↦ v ∗ 
          ▷ (ph ↦ v -∗ |={⊤ ∖ ↑queue_ns, ⊤}=> read_head_token ∗ PE v).
  Proof using PERS_PE.
    iIntros "#INV #ITH #READ #RP0 RH".
    iInv "INV" as "(%hq & %h' & %t_ & %br_ & %fl & %rop_ & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH' & >DQ & #EI)".
    iDestruct "RH'" as "[(% & RH' & RTOK') | TOK']".
    { by iDestruct (read_head_resources_excl with "RH RH'") as "?". }
    iDestruct (read_head_resources_auth_agree with "[$] [$]") as %[<- <-].
    iDestruct (read_head_resources_rop_interp_agree with "[$] [$]") as %<-.

    rewrite /read_hist_interp. iDestruct "RHI" as "(ROPA & ROP & RHIST & %RH_WF & #OLDS)".
    rewrite /rop_interp. iDestruct ("ROP" with "[//]") as "(%r & %rp & READ_ & RP & ROP)".
    iDestruct (ith_read_agree with "READ READ_") as %->. iClear "READ_".

    iDestruct "ROP" as "[SAFE | [-> #CW]]".
    2: { iDestruct (ith_rp_le with "RP RP0") as %CM. inversion CM. }

    iAssert (br_lb h)%I as "#BR_H".
    { iDestruct (take_snapshot with "[$]") as "(_&_&$&_)". }
    iModIntro.

    rewrite /safe_read.
    iDestruct "SAFE" as "[FROM_HEAD | PROT]".
    - iDestruct "FROM_HEAD" as "[<- [-> | (% & -> & RTOK')]]".
      { iDestruct (ith_rp_le with "RP RP0") as %CM. inversion CM. }
      iDestruct (hq_auth_lookup with "[$] ITH") as %HTH.
      iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
      { iIntros (->). iDestruct (queue_interp_cur_empty with "[$]") as %NO.
        specialize (NO 0). rewrite Nat.add_0_r in NO. congruence. }

      (* TODO: add a head element access lemma? *)
      rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
      rewrite /phys_queue_interp. iDestruct "PQI" as "(Q & (%pt_ & TAIL & DUMMY & %LL & HEAD))".
      rewrite lookup_drop Nat.add_0_r. rewrite HTH. iEval (simpl) in "HEAD".

      iDestruct (big_sepL_lookup_acc with "Q") as "[H CLOS']".
      { rewrite lookup_drop. erewrite Nat.add_0_r. eauto. }
      simpl. destruct ndh. iDestruct "H" as "[H NXT]".

      iFrame "H". iIntros "!> H". 

      iDestruct ("CLOS'" with "[$H $NXT]") as "Q".
      iAssert (phys_queue_interp (drop h hq)) with "[Q TAIL DUMMY HEAD]" as "PQI".
      { iFrame.
        rewrite lookup_drop. erewrite Nat.add_0_r. rewrite HTH.
        by iFrame. }
      iAssert (queue_interp hq h t h fl) with "[PQI BR FL]" as "QI".
      { iFrame. iSplit; [done| ]. by rewrite HTH. }

      iDestruct (finish_read_op with "RH [ROPA RHIST RP RTOK'] [$] [$]") as "X".
      { by right. }
      { iFrame. iFrame "OLDS". iSplit; [| done].
        iFrame. iIntros (? [=<-]). iFrame "RP READ".
        iLeft. rewrite /safe_read. iLeft.
        iSplit; [done| ]. iRight. by iFrame. }
      iMod "X" as "(%hist' & RH & RHI & RTOK)".
      iSpecialize ("RTOK" with "[]").
      { iPureIntro. constructor. }

      iDestruct (queue_elems_interp_get with "[$]") as "?"; eauto.
      iFrame.
      iMod ("CLOS" with "[-]") as "_"; [| done].
      iFrame. iFrame "EI".
      iNext. iSplit; [done| ].
      iLeft. iFrame.
    -
      (* TODO: rewrite the invariant into this form *)
      iAssert (⌜ rp = rs_proc (Some rsp_protected)⌝ ∗ rop_token ∗ ⌜ h = h' - 1 /\ is_Some od \/ h = fl ⌝)%I with "[PROT]" as "(-> & RTOK & %CASES)".
      { iDestruct "PROT" as "[((-> & ? & %) & -> & TOK) | ((? & ->) & -> & TOK)]"; iFrame.
        all: iPureIntro; tauto. }

      iDestruct (hq_auth_lookup with "[$] ITH") as %HTH.
      iAssert (▷ ph ↦ ndh.1 ∗ ▷ (ph ↦ ndh.1 -∗ dangle_interp od h' hq ∗ queue_interp hq h' t h fl ∗ PE ndh.1))%I
        with "[DANGLE QI]" as "[PH PH']".
      { destruct CASES as [(-> & OD) | ->].
        - inversion OD. subst.
          rewrite /dangle_interp.
          iDestruct "DANGLE" as "(DAUTH & x)".
          iDestruct "x" as "[% | (-> & HN_D)]"; [done| ].
          rewrite HTH.
          simpl. destruct ndh. iDestruct "HN_D" as "[H NXT]".
          iDestruct (queue_elems_interp_get _ _ (h' - 1) with "EI") as "PEv"; eauto.
          iFrame. iFrame "PEv".
          iNext. iIntros. iRight. by iFrame.
        - rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
          iDestruct "FL" as "(% & %FLTH_ & FL & HNI_FL)".
          rewrite HTH in FLTH_. inversion FLTH_. subst.
          simpl. destruct ndh. iDestruct "HNI_FL" as "[H NXT]".
          iDestruct (queue_elems_interp_get _ _ fl with "EI") as "PEv"; eauto.
          iFrame. iFrame "PEv".
          iNext. iIntros. iSplit; [by eauto| ].
          iExists _. rewrite HTH. iSplit; [done| ]. iFrame. }

      iFrame "PH". iIntros "!> PH".  
      iDestruct ("PH'" with "[$]") as "(DANGLE & QI & PEv)".
      
      iDestruct (finish_read_op with "RH [ROPA RHIST RP RTOK] [$] [$]") as "X".
      { by right. }
      { iFrame. iFrame "OLDS". iSplit; [| done].
        iFrame. iIntros (? [=<-]). iFrame "RP READ".
        iLeft. rewrite /safe_read. iRight.
        destruct CASES as [(-> & OD) | ->].
        - iLeft. iFrame. iPureIntro. done.
        - iRight. iFrame. iPureIntro. done. }
      iMod "X" as "(%hist' & RH & RHI & RTOK)".
      iSpecialize ("RTOK" with "[]").
      { iPureIntro. constructor. }

      iFrame.
      iMod ("CLOS" with "[-]") as "_"; [| done].
      iFrame. iFrame "EI". iNext. iSplit; [done| ]. iLeft. iFrame.
  Qed.

  Lemma read_head_close_cancelled_vs h ph ndh t i pt:
    queue_inv PE -∗ ith_node h (ph, ndh) -∗ ith_read i h 0 -∗ 
    read_head_resources t h pt (Some i) -∗ ith_rp i rs_canceled -∗ rop_token -∗
    |={⊤}=> read_head_token.
  Proof using PERS_PE.
    iIntros "#INV #ITH #READ RH #CNC TOK".    
    iInv "INV" as "(%hq & %h' & %t_ & %br_ & %fl & %rop_ & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH' & >DQ & #EI)".    
    iDestruct "RH'" as "[(% & RH' & RTOK') | TOK']".
    { by iDestruct (read_head_resources_excl with "RH RH'") as "?". }
    iDestruct (read_head_resources_auth_agree with "[$] [$]") as %[<- <-].
    iDestruct (read_head_resources_rop_interp_agree with "[$] [$]") as %<-.
    
    rewrite /read_hist_interp. iDestruct "RHI" as "(ROPA & ROP & RHIST & %RH_WF & #OLDS)".
    rewrite /rop_interp. iDestruct ("ROP" with "[//]") as "(%r & %rp & READ_ & RP_ & ROP)".
    iDestruct (ith_read_agree with "READ READ_") as %->. iClear "READ_".
    iDestruct (ith_rp_le with "CNC RP_") as %CM. inversion CM. subst rp.
    
    iAssert (br_lb h)%I as "#BR_H".
    { iDestruct (take_snapshot with "[$]") as "(_&_&$&_)". }
    
    iDestruct (finish_read_op with "RH [ROPA RHIST CNC ROP] [$] [$]") as "X".
    { by left. }
    { iFrame. iFrame "OLDS". iSplit; [| done].
      iFrame. iIntros (? [=<-]). iFrame "CNC READ ROP". }
    iMod "X" as "(%hist' & RH & RHI & RTOK_)". iClear "RTOK_". 
    
    iDestruct (hq_auth_lookup with "[$] ITH") as %HTH.
    iFrame "TOK'".  
    iMod ("CLOS" with "[-]") as "_"; [| done]. 
    
    iFrame. iNext. iSplit; [done| ]. iFrame "EI". iLeft. iFrame.
  Qed.

  Lemma check_head_change_vs t pt h ndh i ph
    (PTR_NEQ: pt ≠ ph):
    queue_inv PE -∗ read_head_resources t h pt (Some i) -∗ rop_token -∗
    ith_node h (ph, ndh) -∗ ith_read i h 0 -∗ disj_range h t -∗ 
    |={⊤, ⊤ ∖ ↑queue_ns}=> ∃ (ph': loc), ▷ Head ↦{1 / 2} #ph' ∗ 
        ▷ (Head ↦{1 / 2} #ph' -∗ |={⊤ ∖ ↑queue_ns, ⊤}=> 
             ∃ rp, read_head_resources t h pt (Some i) ∗
             ith_rp i rp ∗ (⌜ ph' = ph /\ rp = rs_proc None ⌝ ∨ ⌜ ph' ≠ ph /\ rp = rs_canceled ⌝ ∗ rop_token )).
  Proof using.
    clear PERS_PE.
    iIntros "#INV RH TOK #ITH #READ #DISJ".

    iInv "INV" as "(%hq & %h' & %t_ & %br_ & %fl & %rop_ & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH' & >DQ & EI)".
    iModIntro.
    iDestruct "RH'" as "[(% & RH' & RTOK') | TOK']".
    { by iDestruct (read_head_resources_excl with "RH RH'") as "?". }
    iDestruct (read_head_resources_auth_agree with "[$] [$]") as %[<- <-].
    iDestruct (read_head_resources_rop_interp_agree with "[$] [$]") as %<-.

    iDestruct (access_queue_ends with "[$] [$]") as "(%ph' & %pt_ & HEAD & TAIL & #HT & CLOS')".
    iDestruct (read_head_res_Tail_agree with "RH [$]") as %EQ.
    inversion EQ. subst pt_. clear EQ.
    iFrame "HEAD". iIntros "!> HEAD".    

    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".
    iFrame "RH".
    iClear "INV".

    rewrite /read_hist_interp. iDestruct "RHI" as "(ROPA & ROP & RHIST & %RH_WF & #OLDS)".
    rewrite /rop_interp. iDestruct ("ROP" with "[//]") as "(%r & %rp & READ_ & RP & ROP)".
    iDestruct (ith_read_agree with "READ READ_") as %->. iClear "READ_".

    iDestruct "ROP" as "[SAFE | [-> #CW]]".
    2: { iDestruct (bi.persistent_sep_dup with "RP") as "[$ #RP]". 
         iFrame. iRight. iFrame.
         rewrite /cancel_witness.
         iDestruct "CW" as "(% & %GT & #LB)".
         iAssert (⌜ r' <= h' ⌝)%I as %?.
         { iDestruct (me_auth_lb with "[AUTHS] LB") as %?; [| done]. 
           by iDestruct "AUTHS" as "(?&_)". }
         iApply fupd_trans_frame. iSplitL.
         2: { iModIntro. iApply bi.True_sep'. iSplit; [| done].
              iIntros (->). 
              iDestruct "HT" as "[[? ->] | ((%LT & NEQ') & (%nd' & ITH'))]"; [done| ].
              rewrite /disj_range. 
              iDestruct ("DISJ" with "[] ITH ITH'") as %DISJ.
              { iPureIntro. rewrite !elem_of_set_seq. lia. }
              done. }
         iIntros "_".

         iAssert (rop_interp (Some i) h' h fl od)%I as "ROP".
         { rewrite /rop_interp. iIntros (? [=<-]).
           do 2 iExists _. iFrame "RP". iSplit. 
           { iApply (ith_included with "READ"). lia. }
           iRight. iSplit; [done| ].
           iExists _. by iFrame "LB". }
         iAssert (read_hist_interp hist (Some i) h' h fl od) with "[ROPA ROP RHIST]" as "RHI".
         { by iFrame "#∗". }

         iMod ("CLOS" with "[-]") as "_"; [| done].
         by iFrame. }

    rewrite /safe_read.
    iDestruct "SAFE" as "[FROM_HEAD | PROT]".
    2: { iAssert (rop_token)%I with "[PROT]" as "RTOK'".
         { iDestruct "PROT" as "[((% & % & %X) & ? & RTOK') | ([% %] & % & RTOK')]"; iFrame. }
         by iDestruct (rop_token_excl with "[$] [$]") as "?". } 
    iDestruct "FROM_HEAD" as "[<- [-> | (% & -> & RTOK')]]".
    2: { by iDestruct (rop_token_excl with "[$] [$]") as "?". }
    
    destruct RH_WF as (n & DOM & ROP & SEQ & BB).
    iDestruct (ith_read_hist_compat with "[$] [$]") as %(?&rpa&NTH&_). 
    iDestruct (ith_rp_hist_compat with "[$] [$]") as %(xx&NTH_&RS_LE).
    rewrite NTH in NTH_. inversion NTH_. subst xx. clear NTH_.
    inversion RS_LE. subst.

    iDestruct (read_hist_update' with "RHIST RP") as "X".
    { apply rs_init_going. }
    { apply NTH. }
    erewrite Nat.max_id. rewrite decide_False; [| done].
    iMod "X" as "(RHIST & #READ' & RP)". 
    
    iDestruct "HT" as "[[%GE ->] | ((%LT & NEQ') & (%nd' & ITH'))]".
    { red in ORDER. assert (h = t) as -> by lia.
      iDestruct (hq_auth_lookup with "[$] [$]") as %TTH.
      rewrite /queue_interp. iDestruct "QI" as "(-> & _)".
      apply mk_is_Some, lookup_lt_is_Some in TTH. lia. }
    iDestruct (ith_node_agree with "ITH' ITH") as %EQ.
    inversion EQ. subst ph' nd'. clear EQ.
    iDestruct (ith_rp_get_rs_p0 with "RP") as "#RP0".
    { constructor. }
    (* TODO: make/find a lemma *)
    iApply fupd_trans_frame. iSplitL.
    2: { iModIntro. iApply bi.True_sep'. iFrame "RP0". set_solver. }
    iIntros "_".

    iAssert (rop_interp (Some i) h h fl od)%I with "[TOK RP]" as "ROP".
    { rewrite /rop_interp. iIntros (? [=<-]).
      do 2 iExists _. iFrame "RP". iSplit. 
      { iApply (ith_included with "READ"). lia. }
      iLeft. rewrite /safe_read. iLeft. iSplit; [done| ].
      iRight. iFrame. done. }
    set (hist' := <[i:=(h, x, rs_proc (Some rsp_going))]> hist). 
    iAssert (read_hist_interp hist' (Some i) h h fl od) with "[ROPA ROP RHIST]" as "RHI".
    { iFrame "#∗". iSplit.
      2: { iApply old_rps_olds.
           rewrite old_rps_olds.
           replace (delete i hist') with (delete i hist); [done| ].
           subst hist'. by rewrite delete_insert_delete. }
      iPureIntro. red. 
      exists n. split; [| split; [| split]]. 
      - rewrite dom_insert_L. rewrite DOM.
        apply mk_is_Some, elem_of_dom in NTH. set_solver. 
      - tauto.
      - intros ?????. rewrite !lookup_insert_Some.
        intros [(? & ?) | (? & ITH) ] [(? & ?) | (? & JTH) ]; subst; simpl in *; try lia.
        + eapply SEQ in H; eauto. done. 
        + eapply BB; eauto. 
        + eapply SEQ in H; eauto; try done.
      - intros ??. rewrite lookup_insert_Some.         
        intros [(? & ?) | (? & ITH) ]; subst; simpl; try lia.
        + eapply BB in NTH; eauto.
        + eapply BB in NTH; eauto. }

    iMod ("CLOS" with "[-]") as "_"; by iFrame.
  Qed.

End ReadHeadViewshifts.
