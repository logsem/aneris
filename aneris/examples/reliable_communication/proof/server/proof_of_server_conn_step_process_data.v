From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang Require Import ast tactics.
From iris.algebra.lib Require Import excl_auth.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_proof.
From aneris.aneris_lang.lib Require Import lock_proof queue_proof map_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.resources Require Import
     chan_session_resources socket_interp.
From aneris.examples.reliable_communication.proof.common_protocol Require Import
     proof_of_recv_on_chan.
From aneris.examples.reliable_communication.proof.server Require Import
     server_resources.

Section Proof_of_server_conn_step_3.
  Context `{!anerisG Mdl Σ}.
  Context `{!Reliable_communication_service_params}.
  Context `{!chanG Σ, !lockG Σ}.
  Context `{!server_ghost_names}.

  Notation srv_ip := (ip_of_address RCParams_srv_saddr).

  (** We have different cases to consider, depending on whether
          -  m ∈ R or (m ∉ R ∗ server_interp m)
          -  the value mval is INIT, COOKIE, ACKID, or SEQID. *)
  (** If the msg is
            -- INIT: can be ingored
            -- COOKIE: then two cases:
               -- m ∈ R: should be handled, by knowing that COOKIE-ACK has been sent back;
               -- m ∉ R: should be absurd by knowing that we have cookieRes twice;
            -- ACKID or SEQID, handled by process_data_on_chan. *)


  (** We start by factoring out the case when the msg is ACKID or SEQID. *)
  Lemma server_conn_step_process_data_spec_transmission_data
        (skl : loc) (skt_passive : val)
        skt sock h (cml : loc) cmv (cql : loc) qlk γqlk mval m
       (cM :gmap socket_address conn_state)
       (γM : session_names_map) (R0 T0: gset message)
       cdata ck ackId sidLBid :
    skt_passive = (skt, #cml, (#cql, qlk))%V →
    dom γM = dom cM →
    m_sender m ∈ dom cM →
    cM !! m_sender m = Some (Connected (cdata, ck, (ackId, sidLBid))) →
    is_map cmv cM →
    m_destination m = RCParams_srv_saddr →
    saddress sock = Some RCParams_srv_saddr →
    sblock sock = true →
    {{{ is_skt_val skt h Right ∗
        is_conn_queue_lock γqlk qlk cql ∗
        RCParams_srv_saddr ⤇ server_interp ∗
        m_sender m ⤇ client_interp ∗
        inv (RCParams_srv_N.@"skt") (socket_inv_def h RCParams_srv_saddr sock Right) ∗
        skl ↦[srv_ip]{1 / 3} InjRV (#cql, qlk) ∗
        cml ↦[srv_ip] cmv ∗
        known_sessions γM ∗
        own γ_srv_known_messages_R_name (◯ ({[m]} ∪ R0)) ∗
        own γ_srv_known_messages_R_name (● ({[m]} ∪ R0)) ∗
        own γ_srv_known_messages_T_name (◯ T0) ∗
        ([∗ set] m ∈ R0, ⌜(m_sender m) ∈ dom γM⌝) ∗
        ([∗ set] m ∈ R0, message_conn_map_resources cM m) ∗
        ([∗ map] sa↦st ∈ cM, session_map_resources sa st R0 T0) ∗
        ⌜s_is_ser (msg_serialization RCParams_clt_ser) mval (m_body m)⌝ ∗
        ((∃ (str : string) (i : nat), ⌜mval = InjLV (#str, #i)⌝ ∗
                  (⌜str = "INIT"⌝ ∗ ⌜i = 0⌝ ∨ ⌜str = "COOKIE"⌝ ∗
                   (∃ γs : session_name, session_token (m_sender m) γs)))
               ∨ (∃ γs : session_name, session_connected (m_sender m) γs) ∗
               ((∃ ackid : val, ⌜mval = InjRV (InjLV ackid)⌝ ∗
                   (∃ n : nat, ⌜ackid = #n⌝ ∗ ack_interp_pers (m_sender m) n Right))
                ∨ (∃ (i : Z) (w : val), ⌜mval = InjRV (InjRV (#i, w))⌝ ∗
                     (∃ n : nat, ⌜Z.of_nat n = i⌝ ∗ idmsg_interp_pers (m_sender m) n w Right)))) ∗
        (⌜m ∈ R0⌝ ∨ (server_interp m)) ∗
        (∃ mvalr, ⌜mval = InjRV mvalr⌝)

    }}}
      server_conn_step_process_data (skt, #cml, (#cql, qlk))%V
       (cdata, #ck, (#ackId, #sidLBid))%V mval #(m_sender m) @[srv_ip]
    {{{ v, RET v; ⌜v = #()⌝ ∗ isServer_listening_loop_resources skt_passive }}}.
  Proof.
    iIntros (Hsrv_skt Hdom Hdomc Hsm Hmap Hdest Hsaddr Hsblk Φ).
    iIntros "(%Hskt & #Hqlk & #Hsi & #Hcsi & #Hsinv & Hspat) HΦ".
    iDestruct "Hspat" as
      "(Hskl & Hcml & HknM & #HmRFrag & HmRFull & #HmTfrag & #HdomR & #HmsgRres
             & HknRes & %Hser & HmvalRes & Hres & %Hrval)".
    wp_lam.
    rewrite Hskt.
    wp_pures.
    assert (is_Some (γM !! (m_sender m))).
    { apply elem_of_dom. by rewrite Hdom. }
    destruct Hrval as (mvalr & ->).
    assert (∃ γs, γM !! (m_sender m) = Some γs) as (γs0 & Hmγs).
    { assert (is_Some (γM !! (m_sender m))).
      { apply elem_of_dom. by rewrite Hdom. }
      naive_solver. }
    iDestruct "HmvalRes" as "[(%x & %y & %Habs & _)|#HmvalRes]"; first done.
    iDestruct (big_sepM_lookup_acc _ cM (m_sender m) _ with "[$HknRes]")
      as "(HchanRes & HknResAcc)"; first done.
    iDestruct "HchanRes" as (γs1 ck1) "((#Htk0 & HCkF & %Hhst1 & %Hst2) & HchanRes)".
    iDestruct "HchanRes" as "[(%Habs & _)|HchanRes]"; first by naive_solver.
    iDestruct "HchanRes" as (γc c sidLB_l sidLB_n ackId_l ackId_n) "HchanRes".
    iDestruct "HchanRes" as
      "(%Hhst3 & %Hhst4 & %Hchan & #Hopened & Hckf & HsL & HaL & #Hmono & #Hpers)".
    iDestruct "Hpers" as
      (γs' sa sbuf slk rbuf rlk Hc) "Hpers".
    iDestruct "Hpers"
      as "(%Hgeq & %Hgleq & #Htk' & #HaT & #HiT & Hslk & Hrlk)".
    inversion Hchan.
    iDestruct (session_token_agree with "Htk0 Htk'") as "<-".
    wp_pures.
    rewrite -Hskt.
    (* We call the receiving packets processing function (common to the client/server). *)
    wp_apply (process_data_on_chan_spec
                (RCParams_srv_N.@"skt")
                c srv_ip skt _ _ γc _ sidLB_l ackId_l Right
                mvalr sbuf (m_sender m) slk rbuf rlk sidLB_n ackId_n
               with "[$Hslk $Hrlk $Hsi $HsL $HaL $Hcsi Hsinv $Hmono $Htk0]"); [done ..| | ].
    iSplit; [by iFrame "#"; iExists _, _; iFrame "#"|].
    iDestruct "HmvalRes" as "(_ & [HlRes|HrRes])".
    { iDestruct "HlRes" as (ackid) "[%Hreq [%n [-> [%γ [Htok' Hsidx']]]]]".
      iDestruct (session_token_agree with "Htok' Htk'") as %Heq'.
      iSplit; last eauto.
      iLeft. iExists _. iSplit; [naive_solver|]. iExists _.
      iSplit; [done|]. iExists _. subst. iFrame "#". }
    iDestruct "HrRes" as (i w Heq) "Hmval".
    iSplit; last eauto.
    iRight. iDestruct "Hmval" as (n Hn) "Hmval".
    iExists _, _. iSplit; [naive_solver|].
    iDestruct "Hmval" as (γ') "[Htok' [Hfrag Hsidx'']]".
    iDestruct (session_token_agree with "Htok' Htk'") as %Heq'.
    simplify_eq. simpl in *.
    rewrite Hgeq.
    rewrite Nat.add_1_r.
    iFrame "#".
    (* Postcondition.  *)
    iDestruct 1 as (ridx' ackId') "(HsidLB & Hack & Hsidx'' & %Hridx & %HackId)".
    iApply "HΦ".
    iSplit; first done.
    (* From that point on we reason by case analysis on whether m ∈ R0 or not. *)
    destruct (bool_decide (m ∈ R0)) eqn:HmR0.
    { apply bool_decide_eq_true_1 in HmR0.
      replace ({[m]} ∪ R0) with R0 by set_solver.
      (* Establish loop invariant. *)
      iExists _, _, _, _, _, _.
      iSplit; [done|].
      (* The socket of the server is still in the listening mode. *)
      iSplitL "Hskl"; [done|].
      (* Establish that conn_map_resources hold. *)
      iSplitL.
      subst.
      { iExists R0, T0, cmv.
        iExists γM, cM.
        iFrame "#∗"; eauto.
        do 2 (iSplit; first done).
        iApply "HknResAcc".
        iExists γs1, ck1.
        iSplitL "HCkF".
        iFrame "#∗".
        (iSplit; first done).
        done.
        iRight.
        iExists γc, _, _, _, _, _. iFrame "HsidLB Hack".
        subst; iFrame; eauto. do 3 (iSplit; first done).
        iFrame "#∗".
        iSplit; first by iDestruct "Hopened" as "(_ & Hp)".
        iExists _, _, _, _, _, _. iFrame "#∗"; eauto. }
      iFrame "#∗".
      iExists _, _. iFrame; eauto. }
    apply bool_decide_eq_false_1 in HmR0.
    (* Establish loop invariant. *)
    iExists _, _, _, _, _, _.
    iSplit; [done|].
    (* The socket of the server is still in the listening mode. *)
    iSplitL "Hskl"; [done|].
    (* Establish that conn_map_resources hold. *)
    iSplitL.
    subst.
    { iExists ({[m]} ∪ R0), T0, cmv.
      iExists γM, cM.
      iFrame "#∗"; eauto.
      do 2 (iSplit; first done).
      (* The first part: domain. *)
        iSplit.
      { iApply (big_sepS_insert with "[HdomR]"); first done. simpl.
        iSplit.
        - iPureIntro; rewrite Hdom; set_solver.
        - iApply (big_sepS_mono with "[$HdomR]").
          iIntros. iPureIntro. set_solver. }
      (* The second part: initial shape. *)
      iSplit.
      { iApply (big_sepS_insert with "[$HmsgRres]"); first done.
        iExists _, (InjRV mvalr), _.
        do 2 (iSplit; first done). iRight. eauto; iFrame "#∗". }
      (* Should be a separate lemma. *)
      iAssert ((([∗ map] clt_addr↦st ∈ cM, session_map_resources clt_addr st R0 T0) -∗
                [∗ map] clt_addr↦st ∈ cM, session_map_resources clt_addr st ({[m]} ∪ R0) T0)%I) as
        "Hmono_smr".
      { iIntros "Hhyp".
        iApply (big_sepM_mono with "[$Hhyp]").
        iIntros (k x Hkx) "HchanRes".
        iDestruct "HchanRes" as (γi cki) "((#Htk0i & HCkFi & %Hhst1i & %Hhst2i) & HchanRes)".
        iDestruct "HchanRes" as "[(%Hb & Hc1 & Hc2)|HchanRes]".
        - iExists γi, cki. iSplitL "HCkFi". iFrame "#∗".
          destruct Hhst1i as (y0 & ? & ? & ? & ?).
          destruct Hhst2i as (y1 & ? & ? & ? & ?).
          iSplit.
          { simpl in *. subst.
            iExists y0, _; eauto with set_solver. }
          iExists y1, _; eauto with set_solver.
          iLeft; first by iFrame.
        -  iDestruct "HchanRes" as (γc' c' sidLB_l' sidLB_n' ackId_l' ackId_n') "HchanRes".
           iDestruct "HchanRes"
             as "(%Hhst3i & %Hhst4i & %Hchan' & #Hopened & Hckf & HsL & HaL & #Hmono & #Hpers)".
           iDestruct "Hpers" as
             (γs' sa' sbuf' slk' rbuf' rlk' Hc') "Hpers".
           iDestruct "Hpers"
             as "(%Hgeq' & %Hgleq' & HcT & HaT & HiT & Hslk & Hrlk)".
           inversion Hchan.
           iExists γi, cki. iSplitL "HCkFi". iFrame "#∗".
           destruct Hhst1i as (y0 & ? & ? & ? & ?).
           destruct Hhst2i as (y1 & ? & ? & ? & ?).
           iSplit.
           { simpl in *. subst.
             iExists y0, _; eauto with set_solver. }
           iExists y1, _; eauto with set_solver.
           iRight.
           destruct Hhst3i as (y3 & ? & ? & ? & ? & ? & ?).
           destruct Hhst4i as (y4 & ? & ? & ? & ? & ? & ?).
           subst.
           iExists γc', _, _, _, _, _.
           iFrame "HsL HaL Hckf Hmono Hopened".
           iSplit.
           { iExists y3, (InjLV (#"COOKIE", #cki)). by eauto with set_solver. }
           iSplit.
           { iExists y4, _. by eauto with set_solver. }
            iSplit; first done.
            subst. iExists _, _, _, _, _, _. iFrame "#"; eauto. }
      iApply "Hmono_smr".
      iApply "HknResAcc".
      iExists _, ck1. iFrame "Hopened".
      iFrame "#∗".
      iSplit; first done.
      iRight.
      iExists γc, _, _, _, _, _. iFrame "HsidLB Hack".
      do 3 (iSplit; first done). subst; iFrame; eauto.
      iFrame "#∗".
      iExists _, _, _, _, _, _. iFrame "#∗"; eauto. }
    iFrame "#∗".
    iExists _, _. iFrame; eauto.
  Qed.

  Lemma server_conn_step_process_data_spec
        (skl : loc) (skt_passive : val)
        skt sock h (cml : loc) cmv (cql : loc) qlk γqlk mval m
       (cM :gmap socket_address conn_state)
       (γM : session_names_map) (R0 T0: gset message)
       cdata ck ackId sidLBid :
    skt_passive = (skt, #cml, (#cql, qlk))%V →
    dom γM = dom cM →
    m_sender m ∈ dom cM →
    cM !! m_sender m = Some (Connected (cdata, ck, (ackId, sidLBid))) →
    is_map cmv cM →
    m_destination m = RCParams_srv_saddr →
    saddress sock = Some RCParams_srv_saddr →
    sblock sock = true →
    {{{ is_skt_val skt h Right ∗
        is_conn_queue_lock γqlk qlk cql ∗
        RCParams_srv_saddr ⤇ server_interp ∗
        m_sender m ⤇ client_interp ∗
        inv (RCParams_srv_N.@"skt") (socket_inv_def h RCParams_srv_saddr sock Right) ∗
        skl ↦[srv_ip]{1 / 3} InjRV (#cql, qlk) ∗
        cml ↦[srv_ip] cmv ∗
        known_sessions γM ∗
        own γ_srv_known_messages_R_name (◯ ({[m]} ∪ R0)) ∗
        own γ_srv_known_messages_R_name (● ({[m]} ∪ R0)) ∗
        own γ_srv_known_messages_T_name (◯ T0) ∗
        ([∗ set] m ∈ R0, ⌜(m_sender m) ∈ dom γM⌝) ∗
        ([∗ set] m ∈ R0, message_conn_map_resources cM m) ∗
        ([∗ map] sa↦st ∈ cM, session_map_resources sa st R0 T0) ∗
        ⌜s_is_ser (msg_serialization RCParams_clt_ser) mval (m_body m)⌝ ∗
        ((∃ (str : string) (i : nat), ⌜mval = InjLV (#str, #i)⌝ ∗
                  (⌜str = "INIT"⌝ ∗ ⌜i = 0⌝ ∨ ⌜str = "COOKIE"⌝ ∗
                   (∃ γs : session_name, session_token (m_sender m) γs)))
               ∨ (∃ γs : session_name, session_connected (m_sender m) γs) ∗
               ((∃ ackid : val, ⌜mval = InjRV (InjLV ackid)⌝ ∗
                   (∃ n : nat, ⌜ackid = #n⌝ ∗ ack_interp_pers (m_sender m) n Right))
                ∨ (∃ (i : Z) (w : val), ⌜mval = InjRV (InjRV (#i, w))⌝ ∗
                     (∃ n : nat, ⌜Z.of_nat n = i⌝ ∗ idmsg_interp_pers (m_sender m) n w Right)))) ∗
        (⌜m ∈ R0⌝ ∨ (server_interp m))
    }}}
      server_conn_step_process_data (skt, #cml, (#cql, qlk))%V
       (cdata, #ck, (#ackId, #sidLBid))%V mval #(m_sender m) @[srv_ip]
   {{{ v, RET v; ⌜v = #()⌝ ∗ isServer_listening_loop_resources skt_passive }}}.
  Proof.
    iIntros (Hsrv_skt Hdom Hdomc Hsm Hmap Hdest Hsaddr Hsblk Φ).
    iIntros "(%Hskt & #Hqlk & #Hsi & #Hcsi & #Hsinv & Hspat) HΦ".
    iDestruct "Hspat" as
      "(Hskl & Hcml & HknM & #HmRFrag & HmRFull & #HmTfrag & #HdomR & #HmsgRres
             & HknRes & %Hser & HmvalRes & Hres)".
    iDestruct "HmvalRes" as "[#HlRes|#HrRes]"; last first.
    { iAssert (∃ mvalr, ⌜mval = InjRV mvalr⌝)%I as (mvalr) "Hmvalr".
      { iDestruct "HrRes" as "(_ & [(%a & -> & _)|(%i & %z & -> & _)])"; eauto. }
      rewrite Hskt.
      iApply (server_conn_step_process_data_spec_transmission_data
                _ _ _ _ _ _ _ _ _ _ _ _ cM _ R0 T0  with "[-HΦ] [HΦ]"); [done .. | |].
      do 5 (iSplit; first done).
      iFrame "Hres".
      iFrame "#∗"; eauto.
      iNext. iIntros (v) "(-> & Hh)". iApply "HΦ".
      iSplit; first done.
      rewrite -Hskt Hsrv_skt. iFrame. }
    wp_lam.
    rewrite Hskt.
    wp_pures.
    (* ===================================================================== *)
    (* We proceed by case analysis on whether the message is in R0 or not *)
    (* ===================================================================== *)
    destruct (bool_decide (m ∈ R0)) eqn:HmR0.
    (* Assuming the message is in the set R0 *)
    { apply bool_decide_eq_true_1 in HmR0.
      replace ({[m]} ∪ R0) with R0 by set_solver.
      (* We proceed by case analysis on the shape of the received message's value. *)
      - iDestruct "HlRes" as (s i ->) "Hinit".
        wp_pures.
        iDestruct "Hinit" as "[(-> & ->) |(-> & %γs & #Htk)]".
        (* ----------------------------------------------------------------- *)
        (* Case 1.1: INIT message. *)
        (* ----------------------------------------------------------------- *)
        { case_bool_decide as Hseq; first done.
          wp_pures.
          (* If the msg is INIT, we can simply ignore it. *)
          iApply "HΦ". iSplit; first done.
          (* Now we show that we still have the loop invariant. *)
          (* And we just need to show that resources didn't change. *)
          iExists _, _, _, _, _, _.
          iFrame "#∗".
          iSplit; first done.
          iSplitL "HmRFull Hres HknM HknRes Hcml".
          { iExists _, _, _, _, _.
            iFrame "#∗"; eauto. }
          iExists _, _. iFrame; eauto. }
        (* ----------------------------------------------------------------- *)
        (* Case 1.2: COOKIE message. *)
        (* ----------------------------------------------------------------- *)
        wp_pures.
        (* Case analysis on whether the cookie number received from the client matches. *)
        case_bool_decide as Hckeq.
        (* ----------------------------------------------------------------- *)
        (* Case 1.2.1: Resend the COOKIE-ACK message. *)
        (* ----------------------------------------------------------------- *)
        (* Case 1: If it matches, resend cookie message, as we cannot distinguish between a network duplicate
           and the client resending its request because they don't received the server's COOKIE-ACK message. *)
        { wp_pures.
          assert (∃ γs', γM !! (m_sender m) = Some γs') as (γs' & Hmγs).
          { assert (is_Some (γM !! (m_sender m))).
            { apply elem_of_dom. by rewrite Hdom. }
            naive_solver. }
          wp_apply (s_ser_spec (msg_serialization RCParams_srv_ser)).
          { eauto. iPureIntro. apply (serInit _ 0 Right). }
          iIntros (s1 Hs1). wp_pures.
          iDestruct (big_sepM_lookup_acc _ cM (m_sender m) ((Connected (cdata, ck, (ackId, sidLBid)))) Hsm
                      with "[$HknRes]") as "(HchanRes & HknResAcc)".
          iDestruct "HchanRes" as (γs0 ck0) "((#Htk0 & HCkF & %Hhst1 & %Hst2) & HchanRes)".
          iDestruct "HchanRes" as "[(%Habs & _)|HchanRes]"; first by naive_solver.
          iDestruct "HchanRes" as (γc c sidLB_l sidLB_n ackId_l ackId_n) "HchanRes".
          iDestruct "HchanRes" as "(%Hhst3 & %Hhst4 & %Hchan & #Hopened & Hckf & HsL & HaL & #Hmono & #Hpers)".
          simpl in *.
          destruct Hhst4 as (mm & mv & Hm & Hmser & Hmdest & Hmsend & Hmval).
          assert (m_body mm = s1) as Hmbdy_eq.
          { subst. by apply (msg_ser_is_ser_injective_alt Right _ _ (InjLV (#"COOKIE-ACK", #0))). }
          wp_bind (SendTo _ _ _).
          iInv (RCParams_srv_N.@"skt") as "HsockRes".
          iDestruct "HsockRes" as (R T) "(>Hsh & >Hsa & (>#HrR & >HrT & #HsockRes))". simpl.
          iDestruct "HrT" as (T1 HT1) "HrT".
          iAssert (⌜T0 ⊆ T1⌝)%I as "%HmhrRel".
          {  iDestruct (own_valid_2 with "HrT HmTfrag")
              as %[Hv1%gset_included Hv2]%auth_both_valid_discrete.
             iPureIntro. set_solver. }
          replace s1 with (m_body mm).
          wp_apply (aneris_wp_send_duplicate with "[$Hsa $Hsh]"); [done|done| | |].
          set (mt := {|
                      m_sender := RCParams_srv_saddr;
                      m_destination := m_sender m;
                      m_body := s1
                    |}).
          assert (mt = mm) as Heqmm.
          { rewrite /mt. rewrite -Hmbdy_eq. destruct mm. simplify_eq /=. f_equal. }
          assert (mt ∈ T0) as Ht0 by set_solver.
          set_solver.
          iFrame "#".
          simpl.
          iIntros "[Hsh Hsa] !>".
          iSplitL "Hsh Hsa HrT".
          { iIntros "!>".
            iExists R, T.
            iFrame "#∗". iExists T1. iFrame; eauto. }
          wp_pures.
          iApply "HΦ".
          iSplit; first done.
          iExists _, _, _, _, _, _.
          iFrame "#∗".
          iSplit; first done.
          iSplitL.
          { iExists _, _, _, _, _.
            iFrame "#∗"; eauto.
            do 2 (iSplit; first done).
            iApply "HknResAcc".
            iExists _, ck0. iFrame "#∗".
            iSplit; first done. simpl in *.
            iRight.
            iExists _, _, _, _, _, _.
            iFrame "#∗"; eauto. }
          iExists _, _. iFrame; eauto. }
        (* --------------------------------------------------------------------------------------- *)
        (* Case 1.2.2: the cookie number does not match, we can simply ignore it (even if absurd). *)
        (* --------------------------------------------------------------------------------------- *)
        wp_pures.
        iApply "HΦ". iSplit; first done.
        (* Now we show that we still have the loop invariant. *)
        (* And we just need to show that resources didn't change. *)
        iExists _, _, _, _, _, _.
        iFrame "#∗".
        iSplit; first done.
        iSplitL "HmRFull Hres HknM HknRes Hcml".
        { iExists _, _, _, _, _.
          iFrame "#∗"; eauto. }
        iExists _, _. iFrame; eauto. }
    (* ===================================================================== *)
    (* Now we consider the case when the message m in fresh, i.e. m ∉ R0 *)
    (* ===================================================================== *)
    apply bool_decide_eq_false_1 in HmR0.
    iDestruct "Hres" as "[%Habs|Hres]"; first done.
    (* We again proceed by case analysis on the shape of the received message's value. *)
    assert (∃ γs, γM !! (m_sender m) = Some γs) as (γs & Hmγs).
    { assert (is_Some (γM !! (m_sender m))).
      { apply elem_of_dom. by rewrite Hdom. }
      naive_solver. }
    iDestruct "HlRes" as (s i ->) "Hinit".
    iDestruct "Hinit" as "[(-> & ->) |(-> & %γs' & #Htk')]".
    (* ----------------------------------------------------------------- *)
    (* Case 1.1 INIT CASE. *)
    (* ----------------------------------------------------------------- *)
    (* Absurd case, as we can show that m is actually in R0. *)
    { iDestruct (big_sepM_lookup _ cM (m_sender m) (Connected (cdata, ck, (ackId, sidLBid))) Hsm with "HknRes")
        as "Habs".
      iAssert ((∃ (m' : message) (mval' : val),
                   ⌜m' ∈ R0⌝ ∗
                     ⌜s_is_ser (msg_serialization RCParams_clt_ser) mval' (m_body m')⌝ ∗
                     ⌜m_destination m' = RCParams_srv_saddr⌝ ∗ ⌜m_sender m' = m_sender m⌝ ∗
                     ⌜mval' = InjLV (#"INIT", #0)⌝)%I) as "%Ha".
      { by iDestruct "Habs" as (γs' ck') "((_ & _ & H1 & _) & _)". }
      destruct Ha as (m' & mval' & Hm' & Hser' & Hdest' & Hsend' & Hv').
      assert (m_body m' = m_body m) as Hmbdy_eq.
      { subst. by apply (msg_ser_is_ser_injective_alt Left _ _ (InjLV (#"INIT", #0))). }
      assert (m = m').
      { destruct m, m'. by simpl in *; subst. }
      set_solver. }
    (* ----------------------------------------------------------------- *)
    (* case 1.2. COOKIE CASE. *)
    (* ----------------------------------------------------------------- *)
    (* Regardless dynamic check, this case is absurd, which we show using
     the validity law governing the cookie resource. *)
    iDestruct (big_sepM_lookup _ cM (m_sender m) (Connected (cdata, ck, (ackId, sidLBid))) Hsm with "HknRes")
      as "Habs".
    { iDestruct "Habs" as (γs'' ck') "(_ & [(%Habs & _) |Habs])"; [naive_solver|].
      iDestruct "Habs" as (??????) "Habs".
      iDestruct "Habs" as "(H1 & _ & %Hcm & _ &  Hck & _)".
      iDestruct "Hres" as (mval' Hser') "(_ & Hres)".
      assert (mval' = InjLV (#"COOKIE", #i)) as ->.
      { subst. by apply (msg_ser_is_ser_injective Left (m_body m) _ (InjLV (#"COOKIE", _))). }
      iDestruct "Hres" as "[Hres|(Hopened' & [(%_ & %H2 & _)|(%_a & %_b & %H2 & _)])]"; [|done.. ].
      iDestruct "Hres" as (???) "(%Habs & (%x & %Hx & Hres))".
      iDestruct "Hres" as "[(-> & _)|(_ & _ & Hres & _ & _)]"; first done.
      by iDestruct (CookieRes_excl with "[$Hck] [$Hres]") as "Habs'". }
  Qed.

End Proof_of_server_conn_step_3.
