From iris.proofmode Require Import tactics.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants mono_nat.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import
     network_util_code network_util_proof lock_proof monitor_proof list_proof queue_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.resources Require Import
     chan_endpoints_resources socket_interp.

Section Proof_of_process_data_on_chan.
  Context `{!anerisG Mdl Σ,
            !Reliable_communication_service_params,
            !chanG Σ,
            !lockG Σ,
            !server_ghost_names}.
  Context (N : namespace).

  Lemma prune_sendbuf_at_ack_spec ip s γc γ_slk slk
        sbuf sidLBLoc ser (msg_ack sidLB : nat) :
    {{{ is_send_lock ip γc γ_slk slk sbuf ser sidLBLoc s ∗
        sidLBLoc ↦[ip]{1/2} #sidLB ∗
        mono_nat_lb_own (lock_idx_name γ_slk) msg_ack }}}
      prune_sendbuf_at_ack slk #sidLBLoc #sbuf #msg_ack @[ip]
    {{{ (sidLB' : nat), RET #(); sidLBLoc ↦[ip]{1/2} #sidLB' ∗ ⌜sidLB ≤ sidLB'⌝ }}}.
  Proof.
    iIntros (Φ) "(#Hslk & HsidLBLoc & Hsidx) HΦ".
    wp_lam. wp_pures. wp_load. wp_pures.
    case_bool_decide.
    { wp_pures. iApply "HΦ". iFrame. iPureIntro. lia. }
    wp_pures.
    wp_apply (monitor_acquire_spec with "Hslk").
    iIntros (v) "(-> & Hlocked & Hlk)".
    iDestruct "Hlk" as (q vs sidLB') "(Hsbuf & %Hq & HsidLBLoc' & Hsidx' & Hvs)".
    wp_pures. wp_load. wp_pures.
    iDestruct (heap_mapsto_agree with "HsidLBLoc HsidLBLoc'") as %Heq.
    assert (sidLB = sidLB')%Z as <- by naive_solver.
    iAssert (sidLBLoc ↦[ip] #sidLB)%I with "[HsidLBLoc HsidLBLoc']"
      as "HsidLBloc".
    { by iSplitL "HsidLBLoc". }
    wp_store. wp_pures. wp_bind (queue_drop _ _).
    rewrite -!Nat2Z.inj_add. rewrite -Nat2Z.inj_sub; [|lia].
    wp_apply wp_queue_drop; [done|].
    iIntros (rv Hrv).
    wp_pures. wp_store.
    iDestruct "HsidLBloc" as "[HsidLBLoc HsidLBLoc']".
    assert (sidLB < S msg_ack) as Hle1 by lia.
    iDestruct (mono_nat_lb_own_valid with "Hsidx' Hsidx") as %[_ Hle2].
    wp_apply (monitor_release_spec with "[$Hslk $Hlocked Hsbuf HsidLBLoc' Hsidx' Hvs]").
    { iExists rv, (drop (msg_ack - sidLB) vs), msg_ack.
      rewrite skipn_length.
      rewrite -!Nat2Z.inj_add.
      replace (msg_ack + (length vs - (msg_ack - sidLB)))
        with (sidLB + length vs) by lia.
      iFrame.
      iSplit; [done|].
      rewrite (big_sepL_take_drop _ _ (msg_ack - sidLB)).
      iDestruct "Hvs" as "[_ Hvs]".
      iApply (big_sepL_impl with "Hvs").
      iIntros "!>" (k v Hlookup) "Hv".
      rewrite -!Nat2Z.inj_add.
      replace (sidLB + (msg_ack - sidLB + k)) with (msg_ack + k) by lia.
      done. }
    iIntros (v ->). wp_pures.
    iApply "HΦ". iFrame. iPureIntro. lia.
  Qed.

  Lemma process_data_on_chan_spec c ip skt sa γs γe ser serf
        (sidLBLoc ackIdLoc : loc) s (mval : val) (sbuf : loc)
        (dst : socket_address) slk (rbuf : loc) rlk (ridx ackId : nat) :
    ip_of_address sa = ip →
    endpoint_chan_name γe = session_chan_name γs →
    lock_idx_name (endpoint_send_lock_name γe) =
      side_elim s (session_clt_idx_name γs) (session_srv_idx_name γs) →
    c = ((#sbuf, slk), (#rbuf, rlk), serf)%V →
    side_elim s dst sa = RCParams_srv_saddr →
    {{{ socket_resource skt sa N s ∗
        dst ⤇ side_elim s server_interp client_interp ∗
        is_recv_lock
          ip (endpoint_chan_name γe) (endpoint_recv_lock_name γe) rlk rbuf ackIdLoc s ∗
        is_send_lock
          ip (endpoint_chan_name γe) (endpoint_send_lock_name γe) slk sbuf ser sidLBLoc s ∗
        session_token (side_elim s sa dst) γs ∗
        mono_nat_lb_own
          (side_elim
             s (session_srv_idx_name γs) (session_clt_idx_name γs)) ackId ∗
        sidLBLoc ↦[ip]{1/2} #ridx ∗
        ackIdLoc ↦[ip]{1/2} #ackId ∗
        ((∃ ackid, ⌜mval = InjLV ackid⌝ ∗
                   ∃ (n:nat), ⌜ackid = #n⌝ ∗
                              ack_interp_pers (side_elim s sa dst) n s) ∨
         (∃ (i:nat) w, ⌜mval = InjRV (#i, w)%V⌝ ∗
                       ses_idx (chan_session_escrow_name (endpoint_chan_name γe)) (dual_side s) i w ∗
                       mono_nat_lb_own
                         (side_elim
                            s (session_srv_idx_name γs) (session_clt_idx_name γs)) (S i))) ∗
        (∃ γs : session_name, session_connected (side_elim s sa dst) γs)
    }}}
      process_data_on_chan skt #dst #sidLBLoc #ackIdLoc c mval @[ip]
    {{{ RET #();
        ∃ (ridx' ackId' : nat),
          sidLBLoc ↦[ip]{1/2} #ridx' ∗
          ackIdLoc ↦[ip]{1/2} #ackId' ∗
          mono_nat_lb_own
            (side_elim
               s (session_srv_idx_name γs) (session_clt_idx_name γs)) ackId' ∗
          ⌜ridx ≤ ridx'⌝ ∗ ⌜ackId ≤ ackId'⌝ }}}.
  (* The relation in the postcondition can be strengthened to relate
     much more precisly ridx' and aid' with previous respective values but also
     the content of the sending and receiving buffers. *)
  Proof.
    iIntros (<- Heqc Heqg -> Hsrv Φ)
            "(#Hskt & #Hdst & #Hrlk & #Hslk & #Htok
                    & #Hsidx & HsidLB & HackId & Hmval & #Hsmode) HΦ".
    iDestruct "Hskt" as (sh sock -> Haddr Hblock) "[#Hinterp #Hsk]".
    wp_lam. wp_pures. wp_load.
    iDestruct "Hmval" as "[Hmval | Hmval]".
    { iDestruct "Hmval" as (ackid) "[-> [%n [-> [%γ' [Htok' Hsidx']]]]]".
      iDestruct (session_token_agree with "Htok' Htok") as %Heq.
      simplify_eq. wp_pures.
      destruct s.
      - simpl in *. rewrite -Heqg.
        wp_apply (prune_sendbuf_at_ack_spec with "[$Hslk $HsidLB $Hsidx']").
        iIntros (sidLB') "[HsidLB %Hle]". iApply "HΦ".
        iExists _, _. by iFrame "#∗".
      - simpl in *. rewrite -Heqg.
        wp_apply (prune_sendbuf_at_ack_spec with "[$Hslk $HsidLB $Hsidx']").
        iIntros (sidLB') "[HsidLB %Hle]". iApply "HΦ".
        iExists _, _. by iFrame "#∗". }
    iDestruct "Hmval" as (i w ->) "[Hfrag #Hsidx']".
    wp_pures.
    case_bool_decide as Hdec.
    { assert (i = ackId) as Hdec_nat by naive_solver.
      wp_pures.
      wp_apply (acquire_spec with "Hrlk").
      iIntros (v) "[-> [Hlocked HR]]".
      iDestruct "HR" as (q vs ridx')
                          "(Hrbuf & %Hq & HackId' & Hridx & Hvs)".
      iDestruct (heap_mapsto_agree with "HackId HackId'") as %Heq.
      assert (ackId = ridx' + length vs) as Heq'.
      { inversion Heq. lia. }
      wp_pures. wp_load. wp_pures.
      wp_apply wp_queue_add; [done|].
      iIntros (q' Hq').
      wp_store.
      iAssert (ackIdLoc ↦[ip_of_address sa] #(ridx' + length vs))%I
        with "[HackId HackId']" as "HackId".
      { rewrite Heq. by iSplitL "HackId". }
      wp_store.
      iDestruct "HackId" as "[HackId HackId']".
      wp_apply (release_spec with
                 "[$Hrlk $Hlocked Hrbuf Hridx Hvs Hfrag HackId']").
      { iExists q', (vs ++ [(#i, w)%V]), ridx'. iFrame.
        iSplit; [done|].
        subst. replace (1)%Z with (Z.of_nat 1%nat) by lia.
        rewrite app_length /= -!Nat2Z.inj_add.
        rewrite Nat.add_assoc. iFrame "HackId'".
        iSplit; [|done].
        iExists w.
        replace (length vs + 0) with (length vs) by lia.
        by iSplit. }
      iIntros (v) "->".
      wp_pures.
      wp_load. wp_pures.
      destruct s.
      { wp_apply (s_ser_spec (msg_serialization RCParams_clt_ser)).
        { iPureIntro. eexists _. right. split; [done|].
          eexists _. left. split; [done|]. eexists _. done. }
        iIntros (s Hser).
        wp_pures.
        wp_bind (SendTo _ _ _).
        iInv N as "IH".
        iDestruct "IH" as (R T) "(Hsh & Hsa & IH)".
        wp_apply (aneris_wp_send with "[$Hsa $Hsh Hsidx']"); [done|done| |].
        { iFrame "Hdst".
          iIntros "!>". rewrite /server_interp.
          iExists (InjRV (InjLV #(i + 1))).
          iSplit; [done|]. iSplit; [done|].
          iRight. iSplit; first done.
          iLeft. iExists _. iSplit; [done|].
          iExists (i+1).
          rewrite Nat2Z.inj_add.
          iSplit; [done|].
          iExists _. iFrame "#∗".
          simpl in *. by rewrite -Nat.add_1_r. }
        iIntros "[Hsh Hsa] !>".
        iSplitL "Hsh Hsa IH".
        { iIntros "!>".
          iExists R,
               ({[{|
                m_sender := sa;
                m_destination := dst;
                m_body := s
                   |}]} ∪ T). iFrame. }
        wp_pures. iApply "HΦ". iExists ridx, (i+1). iFrame.
        rewrite Nat2Z.inj_add.
        rewrite -Nat.add_1_r.
        iFrame "#∗". iSplit; [done|]. iPureIntro. lia. }
      wp_apply (s_ser_spec (msg_serialization RCParams_srv_ser)).
      { iPureIntro. eexists _. right. split; [done|].
        eexists _. left. split; [done|]. eexists _. done. }
      iIntros (s Hser).
      wp_pures.
      wp_bind (SendTo _ _ _).
      iInv N as "IH".
      iDestruct "IH" as (R T) "(Hsh & Hsa & IH)".
      wp_apply (aneris_wp_send with "[$Hsa $Hsh Hsidx']"); [done|done| |].
      { iFrame "Hdst".
        iIntros "!>". simpl.
        iExists (InjRV (InjLV #(i + 1))).
        iSplit; [done|]. iSplit; [done|].
        iRight. iSplit; first done.
        iLeft. iExists _.
        iSplit; [done|]. iExists (i+1).
        rewrite Nat2Z.inj_add.
        iSplit; [done|].
        iExists _. iFrame "#∗".
        by rewrite -Nat.add_1_r. }
      iIntros "[Hsh Hsa] !>".
      iSplitL "Hsh Hsa IH".
      { iIntros "!>". iExists R, ({[{|
                m_sender := sa;
                m_destination := dst;
                m_body := s
              |}]} ∪ T).
        iDestruct "IH" as "(IH1 & (%T0 & %T1 & IH2) & IH3)".
        iFrame "#∗". iExists T0. iFrame; eauto with set_solver. }
      wp_pures. iApply "HΦ". iExists ridx, (i+1). iFrame.
      rewrite Nat2Z.inj_add. rewrite -Nat.add_1_r. iFrame "#∗".
      iSplit; [done|]. iPureIntro. lia. }
    wp_pures. wp_load. wp_pures.
    destruct s.
    { wp_apply (s_ser_spec (msg_serialization RCParams_clt_ser)).
      { iPureIntro. eexists _. right. split; [done|].
        eexists _. left. split; [done|]. eexists _. done. }
      iIntros (s Hser).
      wp_pures.
      wp_bind (SendTo _ _ _).
      iInv N as "IH".
      iDestruct "IH" as (R T) "(Hsh & Hsa & IH)".
      wp_apply (aneris_wp_send with "[$Hsa $Hsh]"); [done|done| |].
      { iFrame "Hdst".
        iIntros "!>". rewrite /server_interp.
        iExists (InjRV (InjLV #(ackId))).
        iSplit; [done|]. iSplit; [done|].
        iRight. iSplit; first done.
        iLeft. iExists _. iSplit; [done|].
        iExists ackId. iSplit; [done|].
        iExists _. by iFrame "#∗". }
      iIntros "[Hsh Hsa] !>".
      iSplitL "Hsh Hsa IH".
      { iIntros "!>". iExists _, ({[{|
                m_sender := sa;
                m_destination := dst;
                m_body := s
              |}]} ∪ T). iFrame. }
      wp_pures. iApply "HΦ". iExists ridx, ackId. iFrame.
      iFrame. iSplit; [done|]. iPureIntro. lia. }
    wp_apply (s_ser_spec (msg_serialization RCParams_srv_ser)).
    { iPureIntro. eexists _. right. split; [done|].
      eexists _. left. split; [done|]. eexists _. done. }
    iIntros (s Hser).
    wp_pures.
    wp_bind (SendTo _ _ _).
    iInv N as "IH".
    iDestruct "IH" as (R T) "(Hsh & Hsa & IH)".
    wp_apply (aneris_wp_send with "[$Hsa $Hsh]"); [done|done| |].
    { iFrame "Hdst".
      iIntros "!>". simpl.
      iExists (InjRV (InjLV #ackId)).
      iSplit; [done|]. iSplit; [done|].
      iRight. iSplit; first done.
      iLeft. iExists _.
      iSplit; [done|]. iExists ackId. iSplit; [done|].
      iExists _. iFrame "#∗". }
    iIntros "[Hsh Hsa] !>".
    iSplitL "Hsh Hsa IH".
    { iIntros "!>".
      iExists R, ({[{|
                m_sender := sa;
                m_destination := dst;
                m_body := s
              |}]} ∪ T).
      iDestruct "IH" as "(IH1 & (%T0 & %T1 & IH2) & IH3)".
      iFrame "#∗". iExists T0. iFrame; eauto with set_solver. }
    wp_pures. iApply "HΦ". iExists ridx, ackId. iFrame "#∗".
    done.
  Qed.

End Proof_of_process_data_on_chan.
