From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth gmap.
From fairness Require Import utils.
From lawyer.nonblocking.examples.queue Require Import simple_queue_utils simple_queue.
From heap_lang Require Import heap_lang_defs lang notation.

Close Scope Z.


Section EnqueueViewshifts.
  Context {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}.  
  Context {QL: QueueG Σ}.
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}. 

  (* TODO: move *)
  Definition is_LL_into_alt (hq: HistQueue) (pt: loc) := 
    (forall (i: nat) (nd nd': HistNode),
        hq !! i = Some nd -> hq !! (S i) = Some nd' -> nd.2.2 = nd'.1) /\
    from_option (fun nd => nd.2.2 = pt) True (last hq).

  (* TODO: move *)
  Lemma is_LL_into_equiv hq pt:
    is_LL_into hq pt <-> is_LL_into_alt hq pt.
  Proof using.
    induction hq.
    { done. }
    destruct a as [? [??]]. simpl.
    destruct hq.
    { split.
      - intros ->. red. set_solver.
      - intros [??]. done. }
    destruct h as [? [??]].
    split.
    - intros [-> LL].
      apply IHhq in LL as [NEXT FIN]. clear IHhq.
      red. split.
      2: done.
      simpl.
      intros. destruct i.
      { simpl in *. set_solver. }
      simpl in *.
      ospecialize * (NEXT i _ _); eauto.
    - intros LL.
      destruct LL as [NEXT FIN].      
      apply proj2 in IHhq. ospecialize * IHhq.
      { red. split; [| done].
        intros. eapply (NEXT (S i)); eauto. }
      split; [| done].
      ospecialize (NEXT 0 _ _ _ _ ); eauto.
  Qed.
  
  (* TODO: move *)
  Lemma is_LL_into_ext l p1 v p2
    (LL: is_LL_into l p1):
  is_LL_into (l ++ [(p1, (v, p2))]) p2.
  Proof using.
    apply is_LL_into_equiv. apply is_LL_into_equiv in LL.
    red. destruct LL as [NEXT FIN]. split.
    2: by rewrite last_snoc. 
    intros.
    pose proof H0 as LEN%lookup_lt_Some. rewrite length_app /= in LEN.
    assert (i < length l) as LEN' by lia. clear LEN.
    red in LEN'. apply Nat.le_lteq in LEN' as [LEN | EQ].
    - rewrite lookup_app_l in H; eauto.
      rewrite lookup_app_l in H0; eauto. lia.
    - rewrite EQ in H0.
      rewrite list_lookup_middle in H0; [| done].
      inversion H0. subst nd'. simpl.
      rewrite last_lookup in FIN. rewrite -EQ /= in FIN.
      rewrite lookup_app_l in H; eauto.
      2: lia.
      by rewrite H in FIN.
  Qed.

  (* TODO: move *)
  Lemma hq_auth_extend hq nd:
    hq_auth hq ==∗ hq_auth (hq ++ [nd]).
  Proof using.
    rewrite /hq_auth.
    iIntros "[AUTH FRAG]".
    rewrite big_sepL_app. iFrame "FRAG".
    rewrite big_sepL_singleton. rewrite Nat.add_0_r.

    assert (length hq ∉ dom $ list_to_imap hq).
    { rewrite list_to_imap_dom. rewrite elem_of_set_seq. lia. }

    replace (to_agree <$> list_to_imap (hq ++ [nd])) with (<[ length hq := to_agree nd ]> (to_agree <$> list_to_imap hq)).
    2: { rewrite -fmap_insert. f_equal.
         rewrite /list_to_imap. simpl.
         rewrite imap_app. simpl.
         rewrite Nat.add_0_r. rewrite list_to_map_app /=.
         rewrite insert_empty. rewrite map_union_comm.
         2: { apply map_disjoint_dom. set_solver. }
         by rewrite -insert_union_singleton_l. }

    rewrite /ith_node. rewrite -own_op.
    iApply (own_update with "[$]").
    apply auth_update_alloc.
    apply alloc_singleton_local_update; [| done].
    apply not_elem_of_dom. by rewrite dom_fmap.
  Qed.

  Lemma dangle_interp_extend od h hq nd:
    dangle_interp od h hq -∗ dangle_interp od h (hq ++ [nd]).
  Proof using.
    rewrite /dangle_interp. iIntros "(?&[?|[-> X]])"; iFrame.
    iRight. iSplit; [done| ].
    destruct lookup eqn:X; try done. simpl.
    erewrite @lookup_app_l_Some; eauto.
  Qed.

  Definition hn_interp_wip (hn: HistNode): iProp Σ := 
    let '(l, (v, nxt)) := hn in
    l ↦{1/2} v ∗ (l +ₗ 1) ↦ #nxt.

  Lemma hn_interp_split hn:
    hn_interp hn ⊣⊢ hn_interp_wip hn ∗ (hn.1 ↦{1/2} hn.2.1).
  Proof using.
    destruct hn as [? [??]]. simpl.
    iSplit.
    - iIntros "[[??] ?]". iFrame.
    - iIntros "((?&?)&?)". iFrame.
  Qed.

  Context (PE: val -> iProp Σ) {PERS_PE: forall v, Persistent (PE v)}. 
    
  Lemma queue_elems_interp_extend hq nd:
    queue_elems_interp PE hq -∗ PE nd.2.1 -∗
    queue_elems_interp PE (hq ++ [nd]).
  Proof using.
    rewrite /queue_elems_interp.
    rewrite big_sepL_app. rewrite big_sepL_singleton.
    iIntros "$ $".
  Qed.

  Lemma start_enqueue_vs:
    queue_inv PE -∗ read_head_token -∗ 
    |={⊤, ⊤ ∖ ↑queue_ns}=> ∃ (pt: loc), ▷ Tail ↦{1/2} #pt ∗
        ▷ (Tail ↦{1/2} #pt -∗ |={⊤ ∖ ↑queue_ns, ⊤}=> hn_interp_wip (pt, dummy_node) ∗
          ∃ (t br: nat), read_head_resources t br pt None).
  Proof using.
    iIntros "#INV TOK".
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH' & >DQ & EI)".
    iModIntro.
    
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph & %pt & HEAD & TAIL & #HT & CLOS')".
    iFrame "TAIL". iIntros "!> TAIL".
    iDestruct "RH'" as "[(%pt_ & RH & RTOK) | TOK']".
    2: by iDestruct (read_head_token_excl with "[$] [$]") as "?".
    iDestruct (read_head_res_Tail_agree with "RH [$]") as %EQ.
    inversion EQ. subst pt_. clear EQ.

    iDestruct ("CLOS'" with "[$] [$]") as "[HQ QI]".

    iAssert (read_head_resources t br pt None ∗ hn_interp_wip (pt, dummy_node) ∗ queue_interp hq h t br fl)%I with "[RH QI RTOK]" as "(RH & TNI' & QI)".
    { rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
      iFrame "BR FL". 
      rewrite /phys_queue_interp. iDestruct "PQI" as "(Q & (%pt_ & TAIL & DUMMY & %LL & HEAD))".
      iFrame "HEAD Q".
      iDestruct (read_head_res_Tail_agree with "RH [$]") as %PT.
      inversion PT. subst pt_. 
      iFrame "RH TAIL". iFrame (T_LEN LL).
      rewrite {1}/tail_interp. iDestruct "DUMMY" as "[TNI' | (% & ? & RTOK')]".
      2: by iDestruct (rop_token_excl with "[$] [$]") as "?".
      iDestruct (hn_interp_split with "TNI'") as "[TNI' TL]".
      iFrame "TNI'".
      rewrite /tail_interp. iRight. iFrame. }
      
    iFrame.
    iMod ("CLOS" with "[-]") as "_"; [| done].
    by iFrame.
  Qed. 

  Lemma upd_tail_value_vs v pt t br:
    queue_inv PE -∗ hn_interp_wip (pt, dummy_node) -∗
    read_head_resources t br pt None -∗ 
    |={⊤, ⊤ ∖ ↑queue_ns}=> ▷ pt ↦ #0 ∗
        ▷ (pt ↦ v -∗ |={⊤ ∖ ↑queue_ns, ⊤}=> hn_interp_wip (pt, (v, Loc 0)) ∗ read_head_resources t br pt None).
  Proof using.
    iIntros "#INV TNI' RH". 
    iInv "INV" as "(%hq & %h & %t_ & %br_ & %fl & %rop_ & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH' & >DQ & EI)".
    iModIntro.
    iDestruct (read_head_resources_auth_agree with "RH [$]") as %[<- <-].
    iDestruct (read_head_resources_rop_interp_agree with "RH [$]") as %<-.

    iDestruct "TNI'" as "[TNI0 TNI1]". 
    iAssert (pt ↦ #0 ∗ read_head_resources t br pt None ∗ ∀ (v': val), pt ↦ v' -∗ queue_interp hq h t br fl ∗ pt ↦{1 / 2} v')%I with "[TNI0 RH QI]" as "(TNI0 & RH & QI)".
    { rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
      iFrame "BR FL". iFrame (T_LEN). 
      rewrite {1}/phys_queue_interp. iDestruct "PQI" as "(Q & (%pt_ & TAIL & DUMMY & %LL & HEAD))".
      iDestruct (read_head_res_Tail_agree with "RH [$]") as %EQ.
      inversion EQ. subst pt_. 
      iFrame "Q RH".
      iDestruct "DUMMY" as "[[TNI0' ?] | (% & TNI0' & RTOK')]".
      { by iDestruct (pointsto_ne with "TNI0' TNI0") as %?. }
      iCombine "TNI0 TNI0'" as "foo".
      rewrite frac_op Qp.half_half. iFrame.
      iIntros (v') "[TNI0 TNI0']". iFrame. iSplit; [| done].
      iRight. iFrame. }

    iFrame "TNI0". iIntros "!> TNI0". 
    iDestruct ("QI" with "[$]") as "[QI TNI0]".

    iFrame. 
    iMod ("CLOS" with "[-]") as "_"; by iFrame.
  Qed. 

  Lemma update_tail_vs pn pt v t br:
    queue_inv PE -∗ hn_interp (pn, dummy_node) -∗ hn_interp_wip (pt, (v, pn)) -∗
    read_head_resources t br pt None -∗ PE v -∗ 
    |={⊤, ⊤ ∖ ↑queue_ns}=> ▷ Tail ↦ #pt ∗
        ▷ (Tail ↦ #pn -∗ |={⊤ ∖ ↑queue_ns, ⊤}=> read_head_resources (S t) br pn None ∗ rop_token).
  Proof using.
    simpl. iIntros "#INV DNI TNI RH PEv".

    iInv "INV" as "(%hq & %h & %t_ & %br_ & %fl & %rop_ & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH' & >DQ & EI)".
    iModIntro. 
    iDestruct (read_head_resources_auth_agree with "RH [$]") as %[<- <-].
    iDestruct (read_head_resources_rop_interp_agree with "RH [$]") as %<-.

    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
    rewrite {1}/phys_queue_interp. iDestruct "PQI" as "(Q & (%pt_ & TAIL & DUMMY & %LL & HEAD))".
    iDestruct (read_head_res_Tail_agree with "RH [$]") as %EQ.
    inversion EQ. subst pt_.

    rewrite {1}/read_head_resources. iDestruct "RH" as "(TE & BRE & TAIL' & ROP)".
    iCombine "TAIL TAIL'" as "TAIL".

    iFrame "TAIL". iIntros "!> [TAIL TAIL']". 

    iAssert (|==> read_head_resources (S t) br pn None ∗ auths h (S t) br fl)%I with "[TE BRE TAIL' ROP AUTHS]" as "X".
    { iFrame "BRE ROP TAIL'".
      rewrite /auths. iDestruct "AUTHS" as "($ & TA & $ & $)".
      rewrite bi.sep_comm. iApply (me_update with "TA [$]"). lia. }
    iMod "X" as "[RH AUTHS]". 
    
    iAssert (phys_queue_interp (drop h (hq ++ [(pt, (v, pn))])) ∗ rop_token)%I
      with "[Q HEAD TAIL DNI TNI DUMMY]" as "[PQI ROP]".
    { rewrite /phys_queue_interp.
      rewrite skipn_app.    
      rewrite (proj2 (Nat.sub_0_le _ _)).
      2: { red in ORDER. lia. }
      simpl. rewrite big_sepL_app big_sepL_singleton. iFrame "Q".

      iDestruct "TNI" as "[TNI0 TNI1]".
      iDestruct "DUMMY" as "[[TNI0' ?] | (% & TNI0' & RTOK')]".
      { by iDestruct (pointsto_ne with "TNI1 [$]") as %?. }
      rewrite -bi.sep_assoc. iSplitL "TNI0 TNI0' TNI1".
      { iCombine "TNI0 TNI0'" as "X".
        rewrite frac_op Qp.half_half. iFrame. }

      iFrame.
      iSplitR.
      { iPureIntro. eapply is_LL_into_ext; eauto. }
      remember (drop h hq) as hq'.
      destruct hq'; done. }

    iAssert (queue_interp (hq ++ [(pt, (v, pn))]) h (S t) br fl)%I 
      with "[PQI BR FL]" as "QI".
    { iFrame. iSplitR.
      { iPureIntro. rewrite length_app /=. lia. }
      iDestruct "BR" as "(% & %BR & BR)". iDestruct "FL" as "(% & %FL & FR & ?)".
      iFrame. iPureIntro.
      split; eapply lookup_app_l_Some; eauto. }

    iDestruct (queue_elems_interp_extend _ (pt, (v, pn)) with "[$] [$]") as "EI'".

    iMod (hq_auth_extend with "[$]") as "HQ".
    iDestruct (dangle_interp_extend with "[$]") as "DANGLE".

    iDestruct "RH'" as "[(%pt_ & RH' & RTOK) | TOK']".
    { by iDestruct (rop_token_excl with "[$] [$]") as %?. }

    iFrame "RH ROP".
    iMod ("CLOS" with "[-]") as "_"; [| done].
    iFrame. iPureIntro. red. red in ORDER. lia.
  Qed.

End EnqueueViewshifts.
