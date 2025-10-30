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

  Lemma finish_read_op t br pt i hist h fl od:
  read_head_resources t br pt (Some i) -∗ read_hist_interp hist (Some i) h br fl od -∗
  br_lb br
 ==∗
  ∃ hist', read_head_resources t br pt None ∗ read_hist_interp hist' None h br fl od.
  Proof using.
    iIntros "RH ROP #BR".
    rewrite {1}/read_hist_interp {1}/read_head_resources.
    iDestruct "ROP" as "(ROPA & ROP & RHIST & %RH_WF & #OLDS)".
    iDestruct "RH" as "(TLA & BRA & TAIL & ROPF)".
    rewrite /rop_interp. iDestruct ("ROP" with "[//]") as "(%r & %rp & READ_ & RP & ROP)". 

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
         iDestruct "GOING" as "[((-> & -> & ?) & ->) | ((-> & ->) & ->)]".
         { inversion RS_LE; subst. iFrame "#∗".
           iPureIntro. red. tauto. }
         inversion RS_LE; subst. iFrame "#∗".
         iPureIntro. red. tauto. }
         
    (* iDestruct "FROM_HEAD" as "(-> & [-> | (<- & ->)])". *)
    (* 2: {  *)
    
    (* iEval (rewrite bi.or_assoc) in "SAFE".  *)

    

    (* iDestruct  *)

    (* iMod (read_hist_alloc with "[$]") as "(AUTH & #READ & %RH_WF' & RP)"; [done| ]. *)
    (* red in RH_WF. *)
    (* destruct RH_WF as (n & DOM & ROP & SEQ & BB). *)
    (* assert (set_fold Init.Nat.max 0 (dom hist) + 1 = S n) as EQ.  *)
    (* { rewrite DOM dom_max_set_fold. lia. } *)
    (* rewrite EQ. rewrite EQ in RH_WF'. *)

    (* iFrame "#∗". *)
    (* iModIntro. iSplitL. *)
    (* 2: { iSplit; [done| ]. *)
    (*      iApply old_rps_olds. rewrite delete_insert; [done| ]. *)
    (*      apply not_elem_of_dom. rewrite DOM. rewrite elem_of_set_seq. lia. } *)
    (* rewrite /rop_interp. iIntros (? [=<-]). *)
    (* iFrame "RP". iExists _. iSplit. *)
    (* { iApply (ith_included with "READ"). lia. } *)
    (* iLeft. rewrite /safe_read. iLeft. iSplit; try done. *)
    (* by iLeft. *)
  Abort.
    
    
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
    iInv "INV" as "(%hq & %h0 & %t & %br & %fl0 & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER0 & QI & DANGLE & OHV & RHI & RH & DQ)".
    
    iApply sswp_MU_wp; [done| ].
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph & %pt & HEAD & TAIL & #HT & CLOS')".
    replace Head with (simple_queue.Head q_sq) by (by rewrite Q_SQ).
    iApply (wp_load with "HEAD"). iIntros "!> HEAD".
    iDestruct "RH" as "[(%pt_ & RH) | TOK']".
    2: { by iDestruct (read_head_token_excl with "[$] [$]") as "?". }
    iDestruct (read_head_res_Tail_agree with "RH [$]") as %EQ.
    inversion EQ. subst pt_. clear EQ. 
    iAssert (h_lb h0)%I as "#H_LB". 
    { iDestruct (take_snapshot with "[$]") as "($&?&?&?)". }
      
    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".
    MU_by_burn_cp. iApply wp_value.

    iMod (start_rop with "RHI RH") as "(%i & %hist' & RHI & RH & #ITH)". 

    iMod ("CLOS" with "[-POST CPS PH RH]") as "_".
    { by iFrame. }
    iModIntro. clear hist hq od fl0 ORDER0 rop hist'. 

    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (! _)%E.
    iInv "INV" as "(%hq & %h1 & %t_ & %br_ & %fl1 & %rop_ & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as ">(HQ & AUTHS & %ORDER1 & QI & DANGLE & OHV & RHI & RH' & DQ)".
    (* iDestruct (h_lb_bound with "[$] [$]") as %H01.  *)
    iApply sswp_MU_wp; [done| ].
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph' & %pt_ & HEAD & TAIL & _ & CLOS')".
    iDestruct (read_head_res_Tail_agree with "RH [$]") as %EQ.
    inversion EQ. subst pt_. clear EQ.
    replace Tail with (simple_queue.Tail q_sq) by (by rewrite Q_SQ).
    iApply (wp_load with "TAIL"). iIntros "!> TAIL".
    iDestruct "RH'" as "[(% & RH') | TOK]".
    { by iDestruct (read_head_resources_excl with "RH RH'") as "?". }
    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".
    MU_by_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[-POST CPS PH RH]") as "_".
    { by iFrame. }
    iModIntro. clear hist hq rop_ ph' od br_ ORDER1 h1 t_ fl1.

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { set_solver. }
    MU_by_burn_cp. iApply wp_value.

    iDestruct "HT" as "[[%EMPTY ->] | ([%NEMPTY %NEQ] & (%ndh0 & #HTH0))]".
    { rewrite bool_decide_true; [| done].

      iApply sswp_MU_wp_fupd; [done| ].
      iClear "H_LB ITH". clear dependent h0.

      iInv "INV" as "(%hq & %h1 & %t_ & %br_ & %fl1 & %rop_ & %od & %hist & inv)" "CLOS".
      iEval (rewrite /queue_inv_inner) in "inv".
      iDestruct "inv" as ">(HQ & AUTHS & %ORDER1 & QI & DANGLE & OHV & RHI & RH' & DQ)".
      iModIntro. 
 
      iApply sswp_pure_step.
      { set_solver. }
      MU_by_burn_cp.
      iDestruct "RH'" as "[(% & RH') | TOK]".
      { by iDestruct (read_head_resources_excl with "RH RH'") as "?". }
      iDestruct (read_head_resources_rop_interp_agree with "[$] [$]") as %<-. 
      iDestruct (read_head_resources_auth_agree with "[$] [$]") as %[<- <-].

      
      iMod ("CLOS" with "[-POST CPS PH TOK]") as "_".
      { 
        
        iFrame. iNext. iSplit; [done| ].
        by iLeft. 
      }


      
      
      pure_steps. iApply "POST". iFrame. }

    rewrite PTR_EQ. 

  

End ReadHead. 
