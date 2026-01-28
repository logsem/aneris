From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From fairness Require Import utils.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From lawyer.nonblocking.examples.queue Require Import simple_queue_utils simple_queue.
(* From lawyer.nonblocking.examples.queue.dequeuer Require Import (* dequeuer_lib *). *)
From heap_lang Require Import heap_lang_defs lang notation.

Close Scope Z.


Section DequeueGhost.
  Context {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}.  
  Context {QL: QueueG Σ}.
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}. 
  
  (* TODO: move *)
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

  (* TODO: move *)
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
    red. destruct FIN as [-> | [-> | [-> | ->]]]; subst; simpl; try by eauto.
  Qed.

  (* TODO: move *)
  Lemma drop_drop_comm: ∀ {A : Type} (l : list A) (n1 n2 : nat),
      drop n1 (drop n2 l) = drop n2 (drop n1 l).
  Proof using.
    intros. rewrite !drop_drop. f_equal. lia.
  Qed.  

  Lemma dequeue_restore_QI 
  (h : nat)
  (ph : loc)
  (vh : val)
  (nxh : loc)
  (fl : nat)
  (hq : HistQueue)
  (t br : nat)
  (HTH : hq !! h = Some (ph, (vh, nxh)))
  (T_LEN : t = length hq)
  (pt : loc)
  (LL : is_LL_into (drop h hq) pt):
  ⊢ ([∗ list] nd ∈ drop h hq, hn_interp nd) -∗
  Tail ↦{1 / 2} #pt -∗ 
  tail_interp pt -∗
  Head ↦{1 / 2} #nxh -∗
  (∃ nbr : HistNode, ⌜hq !! br = Some nbr⌝ ∗ BeingRead ↦ #nbr.1) -∗ 
  (∃ nfl : HistNode, ⌜hq !! fl = Some nfl⌝ ∗ FreeLater ↦ #nfl.1 ∗
    hn_interp nfl) -∗ 
  queue_interp hq (h + 1) t br fl ∗ hn_interp (ph, (vh, nxh)).
  Proof using. 
    iIntros "Q TAIL DUMMY HEAD BL FL".
    rewrite /queue_interp. 
    iFrame.
    rewrite -!bi.sep_assoc.
    iSplit; [done| ].
    iFrame "%".
    pose proof (take_drop_middle _ _ _ HTH) as SPLIT.
    rewrite -SPLIT.
    assert (length (take h hq) = h) as H_LEN. 
    { apply length_take_le. apply lookup_lt_Some in HTH.
      (* simpl in *. lia. *)
      apply Nat.le_lteq. tauto. }
    rewrite drop_app_length'; [| done]. simpl.
    rewrite cons_middle app_assoc.
    rewrite drop_app_length'.
    2: { rewrite length_app /=.
         (* clear -H_LEN. lia. *)
         by rewrite H_LEN. }
    iDestruct "Q" as "[$ $]".
    iSplit.
    { iPureIntro. rewrite -(drop_drop _ _ 1) drop_drop_comm.  
      apply is_LL_into_drop; auto. } 
    rewrite -SPLIT in LL.
    rewrite drop_app_length' in LL; [| done].
    simpl in LL. destruct (drop (S h) hq) eqn:REST.
    all: rewrite REST in LL; rewrite REST /=.
    - subst. simpl. iFrame.
    - simpl. destruct h0 as [? [??]]. simpl.
      destruct LL as [-> ?]. by iFrame.
  Qed.

  (* Lemma queue_elems_interp_shorten (PE: val -> iProp Σ) hq h: *)
  (*   queue_elems_interp PE hq h ⊣⊢ queue_elems_interp PE hq (h + 1) ∗ from_option (PE ∘ fst ∘ snd) True (hq !! h).  *)
  (* Proof using. *)
  (*   rewrite /queue_elems_interp. *)
  (*   rewrite Nat.add_comm'  -skipn_skipn. *)
  (*   rewrite -{3}(Nat.add_0_r h). rewrite -lookup_drop. *)
  (*   remember (drop h hq) as l. rewrite -Heql. clear Heql.  *)
  (*   destruct l. *)
  (*   { simpl. iSplit; set_solver. } *)
  (*   simpl. rewrite drop_0. iSplit; iIntros "[$ $]". *)
  (* Qed. *)

  Context (PE: val -> iProp Σ) {PERS_PE: forall v, Persistent (PE v)}. 

  Lemma dequeue_upd_head_post (τ : locale heap_lang)
    (h : nat) (ph : loc) (vh : val) (nxh : loc) (fl : nat)
    (hq : HistQueue) (t br : nat) (rop : option nat) (hist : read_hist)
  (ORDER : hq_state_wf h t br fl)
  (HTH : hq !! h = Some (ph, (vh, nxh)))
  (NEMPTY : t ≠ h)
  (T_LEN : t = length hq)
  (pt : loc)
  (LL : is_LL_into (drop h hq) pt):
  ith_node h (ph, (vh, nxh)) -∗ 
  @me_exact _ q_me_h h -∗
  @me_exact _ q_me_fl fl -∗
  dangle_frag None -∗
  hq_auth hq -∗
  auths h t br fl -∗
  ([∗ list] nd ∈ drop h hq, hn_interp nd) -∗
  Tail ↦{1 / 2} #pt -∗
  tail_interp pt -∗
  (∃ nbr : HistNode, ⌜hq !! br = Some nbr⌝ ∗ BeingRead ↦ #nbr.1) -∗
  (∃ nfl : HistNode, ⌜hq !! fl = Some nfl⌝ ∗ FreeLater ↦ #nfl.1 ∗
           hn_interp nfl) -∗
  dangle_auth None -∗
  ohv_interp PE -∗
  read_hist_interp hist rop h br fl None -∗
  ((∃ pt0 : loc, read_head_resources t br pt0 None ∗ rop_token)
         ∨ read_head_token) -∗
  dequeue_token -∗
  (▷ (∃ (hq0 : HistQueue) (h0 t0 br0 fl0 : nat) 
                (rop0 od : option nat) (hist0 : read_hist),
                queue_inv_inner PE hq0 h0 t0 br0 fl0 rop0 od hist0) ={
           ⊤ ∖ ↑queue_ns,⊤}=∗ emp) -∗
  Head ↦{1 / 2} #nxh -∗
  Head ↦{1 / 2} #nxh -∗
  queue_elems_interp PE hq -∗
  |={⊤ ∖ ↑queue_ns,⊤}=> 
    (@me_exact _ q_me_h (h + 1) ∗ @me_exact _ q_me_fl fl ∗ Head ↦{1 / 2} #nxh ∗
     dangle_frag (Some h)) ∗
    ∃ i r b : nat, ith_read i r (h + 1) ∗ ⌜r ≤ h⌝ ∗ br_lb b ∗
      (⌜b < r⌝ -∗
       ith_rp i rs_canceled
       ∨ ith_rp i rs_aborted ∨ ith_rp i (rs_proc (Some rsp_completed)))
      (* ∗ PE vh *) (** it is moved from queue_elems_interp to dangle_interp *)
  .
  Proof using PERS_PE. 
    iIntros "#HTH CH CFL DFRAG HQ AUTHS Q TAIL DUMMY BR FL DAUTH OHV RHI RH TOK CLOS HEAD HEAD' #EI".

    iMod (dangle_update _ _ (Some h) with "[$] [$]") as "[DAUTH DFRAG]".

    iAssert (|==> auths (h + 1) t br fl ∗ @me_exact _ q_me_h (h + 1))%I with "[CH AUTHS]" as "UPD".
    { rewrite /auths. iDestruct "AUTHS" as "(AUTH&?&?&?)". iFrame.
      iApply (me_update with "AUTH CH"). lia. }
    iMod "UPD" as "[AUTHS CH]".

    iFrame.

    iDestruct (dequeue_restore_QI with "[$] [$] [$] [$] [$] [$]") as "[QI HNI]".
    all: try by eauto. 

    iDestruct (cancel_rop with "[$]") as "#CNC".
    { red. rewrite Nat.add_1_r. reflexivity. }
    
    iDestruct (take_snapshot with "[$]") as "#SHT".
    iDestruct "SHT" as "(_&_&#BR_LB&_)".

    (* iDestruct (queue_elems_interp_shorten with "EI") as "[EI' PEv]". *)
    (* rewrite HTH /=. *)    

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
        - iDestruct "FROM_BR" as "([-> ->] & -> & ?)". lia. } 

      iClear "HTH".
      iMod ("CLOS" with "[-]") as "_"; [| done].
      iDestruct (queue_elems_interp_get with "EI") as "PEv"; eauto.
      iFrame "QI AUTHS OHV HQ RH DAUTH TOK RHIST ROPA EI". iNext.
      rewrite Nat.add_sub. rewrite HTH /=. 
      
      iSplit.
      { iPureIntro. red. red in ORDER. repeat split; try lia. }
      iSplitL "HNI PEv". 
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
      + iDestruct "HEAD" as "(-> & [-> | (-> & -> & ?)])".
        * iRight. simpl. by iFrame "#∗".
        * iLeft. iRight. iLeft. iFrame.
          iPureIntro. split.
          ** split; [lia | done].
          ** simpl. done. 
      + iDestruct "DANGLE" as "((_ & _ & %) & _)". by destruct H.
      + iDestruct "FL"as "([-> ->] & -> & ?)". 
        iLeft. rewrite /safe_read. iFrame. 
        repeat iRight. iFrame. done.
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
      { iIntros (LT). destruct FIN as [-> | [-> | [-> | ->]]].
        all: try by iFrame.
        iDestruct "LB" as "[LB | [%RS_AB | %RS_CANC]]".
        2, 3: done. 
        iDestruct (br_lb_bound with "[$] [$]") as %?. lia. }

      iMod ("CLOS" with "[-]") as "_"; [| done].
      iFrame "QI AUTHS OHV HQ RH DAUTH TOK RHIST". iNext.
      iExists _. rewrite Nat.add_sub. rewrite HTH /=.
      
      iSplit.
      { iPureIntro. red. red in ORDER. repeat split; try lia. }
      iDestruct (queue_elems_interp_get with "EI") as "PEv"; eauto.
      iSplitL "HNI PEv".
      { iRight. by iFrame. }
      rewrite DOM dom_max_set_fold in RH_WF'.
      destruct RH_WF as (SEQ &  BB). 
      Unshelve. 2: exact None. 
      rewrite bi.sep_assoc.
      iFrame "ROPA EI".
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
        iSplit. 
        { iPureIntro. by apply upd_rp_fin_pres. }
        iDestruct "LB" as "[$ | [-> | ->]]".
        all: simpl; iRight; iPureIntro; tauto. }

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

  Lemma get_to_free_post
  (pbr : loc) (b b1 : nat) ph h fl ndh r i (ndbr1 : Node) (LEb : b ≤ b1)
  pfl (ndfl : Node) (hq : HistQueue) (t br : nat) (rop : option nat) (hist : read_hist)
  (PTR_EQ : pbr = ph)
  (ORDER : hq_state_wf (h + 1) t br fl)
  (HTH : hq !! h = Some (ph, ndh))
  (NEMPTY : t ≠ h)
  (T_LEN : t = length hq)
  (FLTH : hq !! fl = Some (pfl, ndfl)):
  ith_node h (ph, ndh) -∗
  ith_read i r (h + 1) -∗
  br_lb b -∗
  (⌜b < r⌝ -∗ ith_rp i rs_canceled ∨ ith_rp i rs_aborted ∨ ith_rp i (rs_proc (Some rsp_completed))) -∗
  br_lb b1 -∗
  ith_node b1 (ph, ndbr1) -∗
  ith_node fl (pfl, ndfl) -∗
  (⌜∃ nd : Node, hq !! fl = Some (ph, nd)⌝ -∗
                ⌜∃ nd : Node, Some (ph, ndh) = Some (ph, nd)⌝ -∗ False) -∗
  @me_exact _ (@q_me_h Σ QL) (h + 1) -∗
  @me_exact _ (@q_me_fl Σ QL) fl -∗
  simple_queue.Head ↦{1 / 2} #ndh.2 -∗
  dangle_frag (Some h) -∗
  hq_auth hq -∗
  auths (h + 1) t br fl -∗
  phys_queue_interp (drop (h + 1) hq) -∗
  (∃ nbr : HistNode, ⌜hq !! br = Some nbr⌝ ∗
           simple_queue.BeingRead ↦ #nbr.1) -∗
  hn_interp (pfl, ndfl) -∗
  dangle_auth (Some h) -∗
  (let '(v, nxt) := ndh in ph ↦ v ∗ (ph +ₗ 1) ↦ #nxt) -∗
  ohv_interp PE -∗
  read_hist_interp hist rop (h + 1) br fl (Some h) -∗
  ((∃ pt : loc, read_head_resources t br pt None ∗ rop_token)
         ∨ read_head_token) -∗
  dequeue_token -∗
  (▷ (∃ (hq0 : HistQueue) (h0 t0 br0 fl0 : nat)
                (rop0 od : option nat) (hist0 : read_hist),
                queue_inv_inner PE hq0 h0 t0 br0 fl0 rop0 od hist0) ={
           ⊤ ∖ ↑queue_ns,⊤}=∗ emp) -∗
  simple_queue.FreeLater ↦ #ph -∗
  queue_elems_interp PE hq -∗
  |={⊤ ∖ ↑queue_ns,⊤}=>
    ∃ (x : Node) (x0 : nat), (let '(v, nxt) := x in pfl ↦ v ∗ (pfl +ₗ 1) ↦ #nxt) ∗
      @me_exact _ q_me_h (h + 1) ∗ @me_exact _ q_me_fl x0 ∗ simple_queue.Head ↦{
      1 / 2} #ndh.2 ∗ dangle_frag None.
  Proof using.
    clear PERS_PE. 
    iIntros "#HTH #READ #BR0 #NO_FL #BR1 #BRTH1 #FLTH #PFL_NEQ_D".
    iIntros "CH CFL HEAD' DFRAG HQ AUTHS PQI BR HNI_FL DAUTH HNI OHV RHI RH TOK CLOS FL EI".

    iDestruct "BR" as "(%nbr & %BRTH & BR)".
    iDestruct (br_lb_bound with "BR1 AUTHS") as %BR1.

    subst pbr.
    destruct nbr as [pbr nbr].

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

      iMod ("CLOS" with "[-DR HNI_FL]") as "_".
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
          - iDestruct "FROM_DANGLE" as "((-> & -> & _) & -> & ?)".
            iFrame "RP".
            iLeft. rewrite /safe_read. rewrite Nat.add_sub.
            do 2 iRight. by iFrame.
          - iDestruct "FROM_BR" as "([-> ->] & -> & ?)".
            rewrite READ in READ'. inversion READ'. subst r x1 x2.
            apply Nat.le_lteq in BR0 as [BR0 | ->].
            { iSpecialize ("NO_FL" with "[//]"). iExFalso.
              iAssert (∃ rp', ith_rp i rp' ∗ ⌜ rp' = rs_canceled \/ rp' = rs_aborted \/ rp' = (rs_proc (Some rsp_completed))⌝)%I as "(%rp' & RP' & %RP')".
              { iDestruct "NO_FL" as "[$|[$|$]]"; set_solver. }
              iDestruct (ith_rp_le with "RP RP'") as %CM.
              exfalso. clear -RP' CM.
              inversion CM; destruct RP' as [-> | [-> | ->]]; try done.
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
      by iFrame.
    -
      iAssert (dequeue_resources (h + 1) h ndh.2 None)%I with "[CH CFL HEAD' DFRAG]" as "DR".
      { iFrame. }

      iMod ("CLOS" with "[-DR HNI_FL]") as "_".
      { iFrame. iNext. iFrame "OLDS". iFrame (RH_WF). iSplit.
        { rewrite /hq_state_wf. iPureIntro. red in ORDER. lia. }
        iSplitR.
        { by iLeft. }
        rewrite /rop_interp. by iIntros (??). }
      by iFrame.
  Qed.

  Lemma check_BR_post
  (h fl : nat) (ph : loc) (ndh : Node) (i r b0 : nat) (hq : HistQueue)
  (t br : nat) (rop : option nat) (hist : read_hist) (pbr : loc) (nbr : Node)
  (READ_BOUND : r ≤ h)
  (ORDER : hq_state_wf (h + 1) t br fl)
  (HTH : hq !! h = Some (ph, ndh))
  (NEMPTY : t ≠ h)
  (T_LEN : t = length hq)
  (BRTH : hq !! br = Some (pbr, nbr)):    
  ith_read i r (h + 1) -∗
  br_lb b0 -∗
  dangle_frag (Some h) -∗
  hq_auth hq -∗
  auths (h + 1) t br fl -∗
  phys_queue_interp (drop (h + 1) hq) -∗
  (∃ nfl : HistNode, ⌜hq !! fl = Some nfl⌝ ∗ FreeLater ↦ #nfl.1 ∗
           hn_interp nfl) -∗
  dangle_auth (Some h) -∗
  (let '(v, nxt) := ndh in ph ↦ v ∗ (ph +ₗ 1) ↦ #nxt) -∗
  (* PE ndh.1 -∗ *) (** follows from historical queue *)
  ohv_interp PE -∗
  read_hist_interp hist rop (h + 1) br fl (Some h) -∗
  ((∃ pt : loc, read_head_resources t br pt None ∗ rop_token)
         ∨ read_head_token) -∗
  dequeue_token -∗
  (▷ (∃ (hq0 : HistQueue) (h0 t0 br0 fl0 : nat) 
                (rop0 od : option nat) (hist0 : read_hist),
                queue_inv_inner PE hq0 h0 t0 br0 fl0 rop0 od hist0) ={
           ⊤ ∖ ↑queue_ns,⊤}=∗ emp) -∗
  BeingRead ↦ #(pbr, nbr)%core.1 -∗
  queue_elems_interp PE hq -∗
  |={⊤ ∖ ↑queue_ns,⊤}=>
    dangle_frag (if decide ((pbr, nbr).1 = ph) then Some h else None) ∗
    (⌜(pbr, nbr).1 = ph⌝ ∨ ⌜(pbr, nbr).1 ≠ ph⌝ ∗
     (let '(v, nxt) := ndh in ph ↦ v ∗ (ph +ₗ 1) ↦ #nxt) ∗ PE ndh.1) ∗
    ∃ (b' : nat) (ndbr' : Node), br_lb b' ∗ ⌜b0 ≤ b'⌝ ∗
      ith_node b' ((pbr, nbr).1, ndbr').
  Proof using PERS_PE.
    iIntros "#READ #BR0 DFRAG HQ AUTHS PQI FL DAUTH HNI OHV RHI RH TOK CLOS BR #EI".
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
      iDestruct (queue_elems_interp_get _ _ h with "[$]") as "PEv"; eauto. 
      
      iFrame "PEv". 
      iMod ("CLOS" with "[-]") as "_"; [| done]. 

      rewrite /rop_interp.
      destruct rop.
      2: { iFrame "#∗ %". iNext. iSplitR.
           { by iLeft. }
           rewrite /rop_interp. by iIntros (??). }
      
      iDestruct ("ROP" with "[//]") as "(%r_ & %rp & READ_ & RP & ROP)".
      iDestruct (ith_read_hist_compat with "[$] READ_") as %(?&? & READ' & _). 

      iFrame. iFrame "OLDS EI".
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

  Lemma get_head_next_vs h ph v nxt fl od:
  queue_inv PE -∗ ith_node h (ph, (v, nxt)) -∗ dequeue_resources h fl ph od -∗
  |={⊤, ⊤ ∖ ↑queue_ns}=> (ph +ₗ 1) ↦ #nxt ∗ 
    ▷ ((ph +ₗ 1) ↦ #nxt -∗ |={⊤ ∖ ↑queue_ns, ⊤}=> dequeue_resources h fl ph od).
  Proof using.
    iIntros "#INV #HEADhn DR". 
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od' & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
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
    iFrame "NXT".
    iIntros "!> NXT". 
    iDestruct ("CLOS'" with "[$VAL $NXT]") as "[??]".
    iMod ("CLOS" with "[-HEAD FL]") as "_"; by iFrame. 
  Qed.

  Lemma update_ohv_vs v:
    queue_inv PE -∗ PE v -∗
    |={⊤, ⊤ ∖ ↑queue_ns}=> ∃ v0, ▷ OldHeadVal ↦ v0 ∗ 
      ▷ (OldHeadVal ↦ v -∗ |={⊤ ∖ ↑queue_ns, ⊤}=> True).
  Proof using.
    iIntros "INV PEv".
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iModIntro. 
    iDestruct "OHV" as "(% & [OHV _])".
    iFrame "OHV". iIntros "!> OHV". 
    iMod ("CLOS" with "[-]") as "_"; by iFrame.
  Qed.

  (* TODO: merge with dequeue_upd_head_post *)
  Lemma dequeue_upd_head_vs h ph vh (nxh: loc) fl:
    queue_inv PE -∗ ith_node h (ph, (vh, nxh)) -∗ dequeue_resources h fl ph None -∗
    |={⊤, ⊤ ∖ ↑queue_ns}=> ▷ Head ↦ #ph ∗
      ▷ (Head ↦ #nxh -∗ |={⊤ ∖ ↑queue_ns, ⊤}=>
                   dequeue_resources (h + 1) fl nxh (Some h) ∗
                   ∃ i r b, ith_read i r (h + 1) ∗ ⌜ r <= h ⌝ ∗
                               br_lb b ∗
                               (⌜ b < r ⌝ -∗ (ith_rp i rs_canceled ∨ ith_rp i rs_aborted ∨ ith_rp i (rs_proc (Some rsp_completed))))).
  Proof using PERS_PE.
    iIntros "#INV #HTH DR".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iModIntro. 
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-].
    iAssert (▷ ⌜ od_ = None ⌝)%I with "[DR DANGLE]" as "#EQ".
    { iNext. by iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->. }
    rewrite -bi.later_sep. iMod "EQ" as %->. iNext.
    
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
    iFrame "HEAD". iIntros "[HEAD HEAD']".
    iApply (dequeue_upd_head_post with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]"); eauto.
  Qed.

  Lemma check_BR_vs h fl ph ndh i r b0
    (READ_BOUND: r <= h):
    queue_inv PE -∗ ith_node h (ph, ndh) -∗
    dequeue_resources (h + 1) fl ndh.2 (Some h) -∗ ith_read i r (h + 1) -∗ br_lb b0 -∗
    |={⊤, ⊤ ∖ ↑queue_ns}=> ∃ (pbr: loc), ▷ BeingRead ↦ #pbr ∗
      ▷ (BeingRead ↦ #pbr -∗ |={⊤ ∖ ↑queue_ns, ⊤}=>
            dequeue_resources (h + 1) fl ndh.2 (if (decide (pbr = ph)) then Some h else None) ∗
            (⌜ pbr = ph ⌝ ∨ 
             ⌜ pbr ≠ ph ⌝ ∗ hn_interp (ph, ndh) ∗ PE ndh.1) ∗
            ∃ b' ndbr', br_lb b' ∗ ⌜ b0 <= b' ⌝ ∗ ith_node b' (pbr, ndbr')).
  Proof using PERS_PE.
    iIntros "#INV #HTH DR #READ #BR0".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iModIntro. 
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-]. 
    iAssert (▷ ⌜ od_ = Some h ⌝)%I with "[DR DANGLE]" as "#EQ".
    { iNext. by iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->. }

    setoid_rewrite <- bi.later_sep. rewrite -bi.later_exist.  
    iMod "EQ" as %->. iNext. 

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
    iFrame "BR". iIntros "BR". 
    iFrame.
    iDestruct "HNI" as "HNI".
    iApply (check_BR_post with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]"); eauto.
  Qed.
  
  Lemma read_FL_vs fl nd od h:
  queue_inv PE -∗ dequeue_resources h fl nd od -∗
    |={⊤, ⊤ ∖ ↑queue_ns}=> ∃ (pfl: loc), ▷ FreeLater ↦ #pfl ∗
      ▷ (FreeLater ↦ #pfl -∗ |={⊤ ∖ ↑queue_ns, ⊤}=>
          ∃ ndfl, ith_node fl (pfl, ndfl) ∗ dequeue_resources h fl nd od).  
  Proof using.
    iIntros "#INV DR".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & EI)".
    iModIntro. 
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-].
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
    iDestruct "FL" as "(%x & %FLTH & FL & HNI_FL)". 
    iDestruct (hq_auth_get_ith with "[$]") as "#FLTH"; [by eauto| ].
    iFrame "FL". iIntros "!> FL". 
    iMod ("CLOS" with "[-DR]") as "_".
    { by iFrame. }
    rewrite {1}(surjective_pairing x). 
    by iFrame "#∗".
  Qed.

  (* TODO: merge with get_to_free_post *)
  Lemma upd_fl_vs h fl (ph: loc) ndh i r b b1 ndbr1 pfl ndfl
    (READ_BOUND: r <= h)
    (LEb : b ≤ b1):
    queue_inv PE -∗ dequeue_resources (h + 1) fl ndh.2 (Some h) -∗
    ith_node h (ph, ndh) -∗ ith_read i r (h + 1) -∗ br_lb b -∗
    (⌜b < r⌝ -∗ ith_rp i rs_canceled ∨ ith_rp i rs_aborted ∨ ith_rp i (rs_proc (Some rsp_completed))) -∗
    br_lb b1 -∗ ith_node b1 (ph, ndbr1) -∗ ith_node fl (pfl, ndfl) -∗
    |={⊤, ⊤ ∖ ↑queue_ns}=> ▷ FreeLater ↦ #pfl ∗
      ▷ (FreeLater ↦ #ph -∗ |={⊤ ∖ ↑queue_ns, ⊤}=> ∃ hn fl',
             hn_interp (pfl, hn) ∗ dequeue_resources (h + 1) fl' ndh.2 None ∗
             PE ndh.1).
  Proof using PERS_PE. 
    iIntros "#INV DR #HTH #READ #BR0 #NO_FL #BR1 #BRTH1 #FLTH".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH & >DQ & #EI)".
    iModIntro. 
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-]. 
    (* iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->. *)
    iAssert (▷ ⌜ od_ = Some h ⌝)%I with "[DR DANGLE]" as "#EQ".
    { iNext. by iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->. }
    setoid_rewrite <- bi.later_sep. iMod "EQ" as %->.
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
    iFrame "FL". iIntros "!> FL". 

    iDestruct (queue_elems_interp_get _ _ h with "EI") as "PEv"; eauto. 

    iMod (get_to_free_post with "HTH READ BR0 NO_FL BR1 BRTH1 FLTH PFL_NEQ_D [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "X"; eauto.
    iModIntro. iDestruct "X" as "(%&%&$&$&$&$)". done.
  Qed.

End DequeueGhost.
