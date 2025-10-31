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


Section ReadHead.

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.
  (* Existing Instance OHE.  *)
  Context {QL: QueueG Σ}.

  Context (d: Degree).

  Let hGS: heap1GS Σ := iem_phys _ EM.
  Existing Instance hGS.

  Definition read_head_fuel := 100.

  Definition get_head_val: val :=
    λ: "ch1",
      let: "ch2" := !#(Head q_sq) in
      if: "ch1" = "ch2"
      then get_val "ch1"
      else !#(OldHeadVal q_sq)
  .

  (* TODO: move dequeue implementation to the corresponding file too *)
  Definition read_head: val := 
    λ: <>,
       let: "ch" := !#(Head q_sq) in
       let: "ct" := !#(Tail q_sq) in
       if: "ch" = "ct" then NONE
       else
         #(BeingRead q_sq) <- "ch" ;;
         SOME (get_head_val "ch")
  .

  (* TODO: move *)
  Lemma read_head_resources_excl t1 br1 pt1 rop1 t2 br2 pt2 rop2:
    read_head_resources t1 br1 pt1 rop1 -∗ read_head_resources t2 br2 pt2 rop2 -∗ False.
  Proof using.
    simpl. rewrite /read_head_resources.
    iIntros "(X&_) (Y&_)".
    by iApply (me_exact_excl with "X [$]"). 
  Qed.

  Lemma read_head_resources_auth_agree t' br' pt' rop' h t br fl:
    read_head_resources t' br' pt' rop' -∗ auths h t br fl -∗ ⌜ t' = t /\ br' = br ⌝.
  Proof using.
    simpl. iIntros "(T&BR&_) (?&T'&BR'&_)".
    iDestruct (me_auth_exact with "T' T") as %?. 
    iDestruct (me_auth_exact with "BR' BR") as %?.
    done. 
  Qed. 
    
  Lemma read_head_resources_rop_interp_agree t' br' pt' rop' hist rop h br fl od:
    read_head_resources t' br' pt' rop' -∗ read_hist_interp hist rop h br fl od -∗
    ⌜ rop' = rop ⌝.
  Proof using.
    simpl. rewrite /read_hist_interp.  
    iIntros "(T&BR&?&ROP) (ROP'&_)".
    iCombine "ROP' ROP" as "R". 
    iDestruct (own_valid with "R") as %V.
    iPureIntro. symmetry. by apply excl_auth_agree_L.
  Qed.
    
  Lemma read_head_token_excl:
    read_head_token -∗ read_head_token -∗ False.
  Proof using.
    simpl. 
    rewrite bi.wand_curry -own_op.
    iIntros "X". by iDestruct (own_valid with "[$]") as %V.
  Qed. 

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
    
  Lemma rop_update rop1 rop2 rop':
    rop_auth rop1 -∗ rop_frag rop2 ==∗ rop_auth rop' ∗ rop_frag rop'. 
  Proof using.
    simpl. rewrite /rop_auth /rop_frag.
    rewrite bi.wand_curry -!own_op.
    iApply own_update. apply excl_auth_update. 
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

  Lemma read_head_res_Tail_agree t br pt rop pt':
    read_head_resources t br pt rop -∗ Tail q_sq ↦{1 / 2} #pt' -∗ ⌜ pt' = pt ⌝.
  Proof using.
    simpl. rewrite /read_head_resources. iIntros "(_&_&T&?) T'".
    iDestruct (pointsto_agree with "[$] [$]") as %?. set_solver.
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

  Lemma finish_read_op t br pt i hist h fl od rp
    (FIN: rs_fin rp):
    read_head_resources t br pt (Some i) -∗
    read_hist_interp hist (Some i) h br fl od -∗
    br_lb br -∗
    ith_rp i rp
 ==∗
  ∃ hist', read_head_resources t br pt None ∗ read_hist_interp hist' None h br fl od.
  Proof using.
    iIntros "RH ROP #BR RP".
    rewrite {1}/read_hist_interp {1}/read_head_resources.
    iDestruct "ROP" as "(ROPA & ROP & RHIST & %RH_WF & #OLDS)".
    iDestruct "RH" as "(TLA & BRA & TAIL & ROPF)".
    rewrite /rop_interp. iDestruct ("ROP" with "[//]") as "(%r & %rp_ & READ_ & RP' & ROP)".
    iDestruct (ith_rp_le with "RP' RP") as %CM.

    iMod (rop_update _ _ None with "[$] [$]") as "(ROPA & ROPF)".
    iAssert (read_head_resources t br pt None)%I with "[ROPF TAIL TLA BRA]" as "$".
    { iFrame. }

    destruct RH_WF as (n & DOM & ROP & SEQ & BB).
    iDestruct (ith_read_hist_compat with "[$] [$]") as %(?&rpa&NTH&_). 
    iDestruct (ith_rp_hist_compat with "[$] [$]") as %(xx&NTH_&RS_LE).
    rewrite NTH in NTH_. inversion NTH_. subst xx. simpl in *. clear NTH_. 

    iDestruct "ROP" as "[SAFE | [-> #CW]]".
    2: { iModIntro. iFrame "RHIST". iFrame "#∗". iSplitR.
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
         iSplitR.
         { rewrite /rop_interp. by iIntros "% %". }
         iSplit.
         { iPureIntro. red. eexists. eauto. }
         destruct ROP as [[=] | [=]]. subst.
         iApply (old_rps_extend with "[$]").
         { eauto. }
         iDestruct "GOING" as "[((-> & -> & ?) & -> & TOK) | ((-> & ->) & -> & TOK)]".
         { inversion RS_LE; subst. iFrame "#∗".
           iPureIntro. red. tauto. }
         inversion RS_LE; subst. iFrame "#∗".
         iPureIntro. red. tauto. }
         
    iDestruct "FROM_HEAD" as "(-> & [-> | (<- & -> & ?)])".
    { inversion CM. }
    inversion RS_LE. subst. 
    inversion CM; subst.
    - clear -FIN. red in FIN. set_solver.
    - inversion RSP.
  Qed.    

  Definition disj_range (h t: nat): iProp Σ :=
    let range := set_seq h (t - h): gset nat in
    (* ([∗ set] i ∈ range, ∃ nd, ith_node i nd) ∗ *)
    (∀ i j ndi ndj, ⌜ i ≠ j /\ i ∈ range /\ j ∈ range ⌝ -∗
                      □ (ith_node i ndi -∗ ith_node j ndj -∗ ⌜ ndi.1 ≠ ndj.1 ⌝)).

  Goal forall h t, Persistent (disj_range h t).
    apply _.
  Abort. 

  Lemma phys_queue_interp_disj_impl' (pq: HistQueue) i j p
    (LT : i < j)
    (ITH : exists nd, pq !! i = Some (p, nd))
    (JTH : exists nd, pq !! j = Some (p, nd)):
  ([∗ list] nd ∈ pq, hn_interp nd) -∗ False.
  Proof using.
    destruct ITH as [? ITH], JTH as [? JTH].
    (* pose proof ITH as II%mk_is_Some%lookup_lt_is_Some.  *)
    pose proof JTH as JJ%mk_is_Some%lookup_lt_is_Some.
    (* apply Nat.lt_exists_pred in JJ as (k & -> & LE).  *)
    apply Nat.lt_exists_pred in LT as (k & -> & LE).
    apply Nat.lt_exists_pred in JJ as (t & EQ & LE').
    erewrite <- (take_drop_middle _ (S k)); eauto.  
    erewrite <- (take_drop_middle (take _ _) i).
    2: { rewrite lookup_take; [| lia]. eauto. }
    repeat rewrite big_sepL_app. simpl.
    iIntros "((?&X&?) & Y & ?)".
    by iDestruct (hn_interp_ptr_excl with "X Y") as %?.
  Qed.

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
    (* iAssert ([∗ set] i ∈ set_seq h (length hq - h), ∃ nd, ith_node i nd)%I *)
    (*   with "[AUTH]" as "#FRAGS".  *)
    (* { iApply big_sepS_forall. iIntros (i IN). *)
    (*   apply elem_of_set_seq in IN as [HH TT]. *)
    (*   destruct (decide (h <= length hq)); [| lia]. *)
    (*   rewrite -Nat.le_add_sub in TT; [| done]. *)
    (*   pose proof TT as [nd ITH]%lookup_lt_is_Some.  *)
    (*   iDestruct (hq_auth_get_ith with "AUTH") as "#ITH"; [done| ]. *)
    (*   iFrame "ITH". } *)
    (* iSplit; [done| ]. *)
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

  Lemma start_read l (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ queue_inv l ∗ read_head_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d 1 }}}
       !#(Head q_sq) @ τ
    {{{ (ph: loc), RET #ph; th_phase_frag τ π q ∗ rop_token ∗ 
          ∃ t br pt rop, read_head_resources t br pt rop ∗
           (⌜ pt = ph /\ rop = None ⌝ ∨ 
            ∃ i h ndh, ⌜ pt ≠ ph /\ rop = Some i ⌝ ∗ ith_node h (ph, ndh) ∗
                        ith_read i h 0 ∗ ⌜ br <= h ⌝ ∗ disj_range h t) }}}.
  Proof using. 
    simpl. iIntros (Φ) "([#QAT #INV] & TOK & PH & CPS) POST".

    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER0 & QI & DANGLE & OHV & RHI & RH & DQ)".
    
    iApply sswp_MU_wp; [done| ].
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph & %pt & HEAD & TAIL & #HT & CLOS')".    
    iApply (wp_load with "HEAD"). iIntros "!> HEAD".
    iDestruct "RH" as "[(%pt_ & RH & RTOK) | TOK']".
    2: { by iDestruct (read_head_token_excl with "[$] [$]") as "?". }
    iDestruct (read_head_res_Tail_agree with "RH [$]") as %EQ.
    inversion EQ. subst pt_. clear EQ. 
      
    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".
    MU_by_burn_cp. iApply wp_value.

    iApply "POST". iFrame "PH". 

    iDestruct "HT" as "[(%GE & <-) | ((%LT & %NEQ) & (%ndh & #HTH))]".
    - iFrame.
      iMod ("CLOS" with "[-]") as "_".
      { by iFrame. }      
      set_solver.
    - iMod (start_rop with "RHI RH") as "(%i & %hist' & RHI & RH & #ITH)". 
      iFrame.
      iAssert (disj_range h t) with "[QI HQ]" as "#DISJ".
      { rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
        subst. iApply (phys_queue_interp_disj with "[$] [$]"). }
      iFrame "DISJ". 
      iMod ("CLOS" with "[-]") as "_".
      { by iFrame. }
      iRight. iFrame "#∗". iModIntro.
      iExists _. 
      iSplit; [done| ]. 
      iSplit.
      2: { red in ORDER0. iPureIntro. lia. }
      iApply (ith_included with "ITH"). lia. 
  Qed.

  Lemma read_tail_exact l (τ: locale heap_lang) (π: Phase) (q: Qp) t br pt rop:
    {{{ queue_inv l ∗ read_head_resources t br pt rop ∗
        th_phase_frag τ π q ∗ cp_mul π d 1 }}}
       !#(Tail q_sq) @ τ
    {{{ RET #pt; th_phase_frag τ π q ∗ read_head_resources t br pt rop }}}.
  Proof using.
    simpl. iIntros (Φ) "([#QAT #INV] & RH & PH & CPS) POST".

    iInv "INV" as "(%hq & %h & %t_ & %br_ & %fl & %rop_ & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER0 & QI & DANGLE & OHV & RHI & RH' & DQ)".
    
    iApply sswp_MU_wp; [done| ].
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph & %pt_ & HEAD & TAIL & #HT & CLOS')".    
    iDestruct (read_head_res_Tail_agree with "RH [$]") as %EQ.
    inversion EQ. subst pt_. clear EQ. 
    iApply (wp_load with "TAIL"). iIntros "!> TAIL".
    iDestruct "RH'" as "[(% & RH' & RTOK) | TOK']".
    { by iDestruct (read_head_resources_excl with "RH RH'") as "?". }
      
    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".
    MU_by_burn_cp. iApply wp_value.

    iApply "POST". iFrame.
    iMod ("CLOS" with "[-]") as "_".
    { by iFrame. }
    done.
  Qed.

  Lemma rop_token_excl: rop_token -∗ rop_token -∗ False.
  Proof using.
    rewrite /rop_token.
    rewrite bi.wand_curry -!own_op.
    iIntros "X". iDestruct (own_valid with "[$]") as %V.
    done.
  Qed.

  Lemma bump_BR l (τ: locale heap_lang) (π: Phase) (q: Qp) t br pt h ndh i ph
    (BRH: br <= h):
    {{{ queue_inv l ∗ read_head_resources t br pt (Some i) ∗
        rop_token ∗ ith_node h (ph, ndh) ∗
        ith_read i h 0 ∗
        th_phase_frag τ π q ∗ cp_mul π d 1 }}}
       #(BeingRead q_sq) <- #ph @ τ
    {{{ RET #(); th_phase_frag τ π q ∗ 
                 read_head_resources t h pt (Some i) ∗ rop_token }}}.
  Proof using.
    simpl. iIntros (Φ) "([#QAT #INV] & RH & RTOK & #HTH & #READ & PH & CPS) POST".

    iInv "INV" as "(%hq & %h' & %t_ & %br_ & %fl & %rop_ & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER0 & QI & DANGLE & OHV & RHI & RH' & DQ)".
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
    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "BR"). iIntros "!> BR". 
    MU_by_burn_cp. iApply wp_value.

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

    iApply "POST". iFrame. 
    iMod ("CLOS" with "[-]") as "_"; [| done].  
    iFrame. iPureIntro.
    red. split; [| apply ORDER0].
    red in RH_WF. destruct RH_WF as (n & DOM & ROP & SEQ & BB).
    eapply BB in ITH. simpl in ITH. lia.
  Qed.

  Definition small_fuel := 10.

  Lemma ith_rp_get_rs_p0 i rs
    (LE: rs_le (rs_proc None) rs):
    ith_rp i rs -∗ ith_rp i (rs_proc None).
  Proof using.
    rewrite /ith_rp. iApply own_mono.
    apply auth_frag_mono. apply singleton_included_mono.
    apply pair_included. split; [done| ].
    by apply rs_le_incl.
  Qed. 

  Lemma check_head_change l (τ: locale heap_lang) (π: Phase) (q: Qp)
    t pt h ndh i ph
    (PTR_NEQ: pt ≠ ph):
    {{{ queue_inv l ∗ read_head_resources t h pt (Some i) ∗
        rop_token ∗ ith_node h (ph, ndh) ∗
        ith_read i h 0 ∗ disj_range h t ∗ 
        cp_mul π d 1 ∗ th_phase_frag τ π q }}}
      ! #(Head q_sq) @τ
    {{{ (ph': loc), RET #ph'; 
        th_phase_frag τ π q ∗ ∃ rp, read_head_resources t h pt (Some i) ∗
          ith_rp i rp ∗ (⌜ ph' = ph /\ rp = rs_proc None ⌝ ∨ ⌜ ph' ≠ ph /\ rp = rs_canceled ⌝ ∗ rop_token ) }}}.
  Proof using. 
    simpl. iIntros (Φ) "([#QAT #INV] & RH & TOK & #ITH & #READ & #DISJ & CPS & PH) POST".

    iInv "INV" as "(%hq & %h' & %t_ & %br_ & %fl & %rop_ & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER0 & QI & DANGLE & OHV & RHI & RH' & DQ)".
    iDestruct "RH'" as "[(% & RH' & RTOK') | TOK']".
    { by iDestruct (read_head_resources_excl with "RH RH'") as "?". }
    iDestruct (read_head_resources_auth_agree with "[$] [$]") as %[<- <-].
    iDestruct (read_head_resources_rop_interp_agree with "[$] [$]") as %<-.

    iDestruct (access_queue_ends with "[$] [$]") as "(%ph' & %pt_ & HEAD & TAIL & #HT & CLOS')".
    iDestruct (read_head_res_Tail_agree with "RH [$]") as %EQ.
    inversion EQ. subst pt_. clear EQ. 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_load with "HEAD"). iIntros "!> HEAD".
    MU_by_burn_cp. iApply wp_value.

    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".

    iApply "POST". iFrame "PH RH".
    iClear "INV QAT CPS".

    rewrite /read_hist_interp. iDestruct "RHI" as "(ROPA & ROP & RHIST & %RH_WF & #OLDS)".
    rewrite /rop_interp. iDestruct ("ROP" with "[//]") as "(%r & %rp & READ_ & RP & ROP)".
    iDestruct (ith_read_agree with "READ READ_") as %->. iClear "READ_".

    (* iDestruct "HT" as "[[%GE ->] | ((%LT & NEQ') & (%nd' & ITH'))]". *)
    (* { red in ORDER0. assert (h' = t) as -> by lia. *)
      
    (*   iDestruct (hq_auth_lookup with lia.  *)

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
    { red in ORDER0. assert (h = t) as -> by lia.
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

    iMod ("CLOS" with "[-]") as "_"; [| done].
    by iFrame.
  Qed.
               
  Lemma read_ohv_spec τ π q l:
    {{{ queue_inv l ∗ th_phase_frag τ π q ∗ cp_mul π d 1 }}}
      !#(OldHeadVal q_sq) @τ
    {{{ v, RET v; th_phase_frag τ π q }}}.
  Proof using.
    iIntros (Φ) "([#QAT #INV] & PH & CPS) POST".
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER & QI & DANGLE & OHV & RHI & RH & DQ)".
    iDestruct "OHV" as "(% & OHV)". 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_load with "[$]"). iIntros "!> ?".
    MU_by_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[-POST PH]") as "_". 
    { by iFrame. }
    by iApply "POST".
  Qed.

  Lemma get_op_node_val l (τ: locale heap_lang) (π: Phase) (q: Qp)
    t h pt i ph ndh:
    {{{ queue_inv l ∗ read_head_resources t h pt (Some i) ∗
        ith_node h (ph, ndh) ∗ ith_read i h 0 ∗ ith_rp i (rs_proc None) ∗
        cp_mul π d small_fuel ∗ th_phase_frag τ π q }}}
      get_val #ph @τ
    {{{ v, RET #v; th_phase_frag τ π q ∗ read_head_resources t h pt (Some i) ∗
                   ∃ rs, ith_rp i rs ∗ ⌜ rs_fin rs ⌝ }}}.
  Proof using.
    simpl. iIntros (Φ) "([#QAT #INV] & RH & #ITH & #READ & #RP0 & CPS & PH) POST".
    rewrite /get_val. pure_steps.

    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step; [done| ].
    MU_by_burn_cp. rewrite loc_add_0. iApply wp_value.

    iInv "INV" as "(%hq & %h' & %t_ & %br_ & %fl & %rop_ & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER0 & QI & DANGLE & OHV & RHI & RH' & DQ)".
    iDestruct "RH'" as "[(% & RH' & RTOK') | TOK']".
    { by iDestruct (read_head_resources_excl with "RH RH'") as "?". }
    iDestruct (read_head_resources_auth_agree with "[$] [$]") as %[<- <-].
    iDestruct (read_head_resources_rop_interp_agree with "[$] [$]") as %<-.

    rewrite /read_hist_interp. iDestruct "RHI" as "(ROPA & ROP & RHIST & %RH_WF & #OLDS)".
    rewrite /rop_interp. iDestruct ("ROP" with "[//]") as "(%r & %rp & READ_ & RP & ROP)".
    iDestruct (ith_read_agree with "READ READ_") as %->. iClear "READ_".

    iDestruct "ROP" as "[SAFE | [-> #CW]]".
    2: { iDestruct (ith_rp_le with "RP RP0") as %CM. inversion CM. }
    rewrite /safe_read. 
    iDestruct "SAFE" as "[FROM_HEAD | PROT]".
    - iDestruct "FROM_HEAD" as "[<- [-> | (% & -> & RTOK')]]".
      { iDestruct (ith_rp_le with "RP RP0") as %CM. inversion CM. }
      iDestruct (hq_auth_lookup with "[$] ITH") as %ITH.
      iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
      { iIntros (->). iDestruct (queue_interp_cur_empty with "[$]") as %NO.
        specialize (NO 0). rewrite Nat.add_0_r in NO. congruence. }
      


      iApply sswp_MU_wp; [done| ].
      iApply (wp_load with "[$]"). 

      
      iDestruct "HT" as "[[%GE ->] | ((%LT & NEQ') & (%nd' & ITH'))]".
      { red in ORDER0. assert (h = t) as -> by lia.        
        rewrite /queue_interp. iDestruct "QI" as "(-> & _)".
        apply mk_is_Some, lookup_lt_is_Some in TTH. lia. }
      
    
 
      
    2: { iAssert (rop_token)%I with "[PROT]" as "RTOK'".
         { iDestruct "PROT" as "[((% & % & %X) & ? & RTOK') | ([% %] & % & RTOK')]"; iFrame. }
         by iDestruct (rop_token_excl with "[$] [$]") as "?". } 
    
    2: { by iDestruct (rop_token_excl with "[$] [$]") as "?". }

    

    
    

  Lemma get_head_val_spec l (τ: locale heap_lang) (π: Phase) (q: Qp)
    t pt h ndh i ph
    (NEQ: pt ≠ ph):
    {{{ queue_inv l ∗ read_head_resources t h pt (Some i) ∗
        rop_token ∗ ith_node h (ph, ndh) ∗
        ith_read i h 0 ∗ disj_range h t ∗ 
        cp_mul π d small_fuel ∗ th_phase_frag τ π q }}}
      get_head_val #ph @τ
    {{{ v, RET v; th_phase_frag τ π q ∗ read_head_resources t h pt (Some i) ∗
                  ∃ rs, ith_rp i rs ∗ ⌜ rs_fin rs ⌝ }}}.
  Proof using. 
    simpl. iIntros (Φ) "([#QAT #INV] & RH & TOK & #ITH & #READ & #DISJ & CPS & PH) POST".
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
    2: { rewrite bool_decide_false; [| set_solver].
         pure_steps.
         split_cps "CPS" 1. 
         iApply (read_ohv_spec with "[$QAT $INV $CPS' $PH]").
         iIntros "!> % PH".
         iApply "POST". iFrame.
         iPureIntro. red. tauto. }
    
    rewrite bool_decide_true; [| set_solver].
    pure_steps.
    split_cps "CPS" 1.     

  Proof using. 
    simpl. iIntros (Φ) "([#QAT #INV] & RH & TOK & #ITH & #READ & CPS & PH) POST".
    rewrite /get_head_val. 
    pure_steps.

    wp_bind (! _)%E.    



  Lemma read_head_spec l (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ queue_inv l ∗ read_head_token ∗ 
        th_phase_frag τ π q ∗ cp_mul π d read_head_fuel }}}
       read_head #() @ τ
    {{{ (v: val), RET v; th_phase_frag τ π q ∗ read_head_token }}}.
  Proof using.
    simpl. iIntros (Φ) "([#QAT #INV] & TOK & PH & CPS) POST".
    rewrite /read_head. destruct q_sq eqn:Q_SQ.
    pure_steps.

    wp_bind (! _)%E.
    split_cps "CPS" 1.
    replace Head with (simple_queue.Head q_sq) by (by rewrite Q_SQ).
    iApply (start_read with "[$QAT $INV $CPS' $PH $TOK]").
    iIntros "!> %ph (PH & RTOK & (%t & %br & %pt & %rop & RH & CASES))".

    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (! _)%E.
    split_cps "CPS" 1.
    replace Tail with (simple_queue.Tail q_sq) by (by rewrite Q_SQ).
    iApply (read_tail_exact with "[$QAT $INV $CPS' $PH $RH]").
    iIntros "!> (PH & RH)".

    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { set_solver. }
    MU_by_burn_cp. iApply wp_value.

    iDestruct "CASES" as "[[-> ->] | (%i & %h & %ndh & [%NEQ ->] & #ITH & #READ & %BR_H)]". 
    { rewrite bool_decide_true; [| done].
      iApply sswp_MU_wp_fupd; [done| ].

      iInv "INV" as "(%hq & %h & %t_ & %br_ & %fl & %rop_ & %od & %hist & inv)" "CLOS".
      iEval (rewrite /queue_inv_inner) in "inv".
      iDestruct "inv" as ">(HQ & AUTHS & %ORDER0 & QI & DANGLE & OHV & RHI & RH' & DQ)".
      iModIntro. 
      iApply sswp_pure_step.
      { set_solver. }
      MU_by_burn_cp.
      iDestruct "RH'" as "[(% & RH' & RTOK') | TOK']".
      { by iDestruct (read_head_resources_excl with "RH RH'") as "?". }
      iDestruct (read_head_resources_auth_agree with "[$] [$]") as %[<- <-].
      iMod ("CLOS" with "[-PH CPS POST TOK']") as "_".
      { iFrame. iNext. iSplit; [done| ]. iLeft. iFrame. }
      iModIntro.
      pure_steps. iApply "POST". iFrame. }

    rewrite bool_decide_false; [| set_solver].
    pure_steps. 

    wp_bind (_ <- _)%E.
    split_cps "CPS" 1.
    replace BeingRead with (simple_queue.BeingRead q_sq) by (by rewrite Q_SQ). 
    iApply (bump_BR with "[-CPS POST]").
    { apply BR_H. }
    { iFrame "#∗". }
    iIntros "!> (PH & RH & RTOK)".

    wp_bind (Rec _ _ _)%E. pure_steps.
 
    
  

End ReadHead. 
