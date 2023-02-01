From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang Require Import ast tactics.
From iris.algebra.lib Require Import excl_auth.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_proof.
From aneris.aneris_lang.lib Require Import assert_proof lock_proof queue_proof map_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.resources Require Import
     chan_session_resources socket_interp.
From aneris.examples.reliable_communication.proof Require Import
     proof_of_make_new_channel_descr
     proof_of_send_from_chan_loop.
From aneris.examples.reliable_communication.proof.server Require Import
     server_resources.

Section Proof_of_server_conn_step_2.
  Context `{!anerisG Mdl Σ}.
  Context `{!Reliable_communication_service_params}.
  Context `{!chanG Σ, !lockG Σ}.
  Context `{!server_ghost_names}.

  Notation srv_ip := (ip_of_address RCParams_srv_saddr).

  (** We have different cases to consider, depending on whether
            - the value mval is INIT, COOKIE, ACKID, or SEQID.
            - m ∈ R or (m ∉ R ∗ server_interp m) *)
  (** If msg is
            -- INIT:
               -- m ∈ R: should be handled, by knowing that INIT-ACK has been sent back;
               -- m ∉ R: (even though absurd) can be handled as above ;
            -- COOKIE: then two cases:
               -- m ∈ R: absurd because the connection is marked only as half-opened;
               -- m ∉ R: should be handled as a fresh message changing the state;
            -- ACKID or SEQID, then they are absurd. *)
  Lemma server_conn_step_to_establish_conn_spec
      (skl : loc) (skt_passive : val) skt sock h (cml : loc) cmv (cql : loc) qlk γqlk mval m
       (cM :gmap socket_address conn_state)
       (γM : session_names_map) ψclt (R0 T0 : gset message) (cookie : nat) :

    skt_passive = (skt, #cml, (#cql, qlk))%V →
    dom γM = dom cM →
    m_sender m ∈ dom cM →
    cM !! m_sender m = Some (HalfOpened cookie) →
    is_map cmv cM →
    m_destination m = RCParams_srv_saddr →
    saddress sock = Some RCParams_srv_saddr →
    sblock sock = true →
    {{{ is_skt_val skt h Right ∗
        is_conn_queue_lock γqlk qlk cql ∗
        RCParams_srv_saddr ⤇ server_interp ∗
        m_sender m ⤇ ψclt ∗
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
          ((∃ str (i: nat),
           ⌜mval = InjLV (#(LitString str), #(LitInt i))⌝ ∗
             init_interp_pers (m_sender m) str Right i) ∨
             ((∃ γs, session_connected (m_sender m) γs) ∗
          ((∃ ackid,
           ⌜mval = InjRV (InjLV ackid)⌝ ∗
           ∃ (n : nat), ⌜ackid = #n⌝ ∗
                        ack_interp_pers (m_sender m) n Right) ∨
             (∃ i w,
           ⌜mval = InjRV (InjRV (#(LitInt i), w)%V)⌝ ∗
           ∃ n : nat, ⌜Z.of_nat n = i⌝ ∗
                      idmsg_interp_pers (m_sender m) n w Right)))) ∗
        (⌜m ∈ R0⌝ ∨ server_interp m)
    }}}
      server_conn_step_to_establish_conn
      (skt, #cml, (#cql, qlk))%V #cookie mval #(m_sender m) @[srv_ip]
   {{{ v, RET v; ⌜v = #()⌝ ∗ isServer_listening_loop_resources skt_passive }}}.
  Proof.
    iIntros (Hsrv_skt Hdom Hdomc Hsm Hmap Hdest Hsaddr Hsblk Φ).
    iIntros "(%Hskt & #Hqlk & #Hsi & #Hcsi & #Hsinv & Hspat) HΦ".
    iDestruct "Hspat" as
      "(Hskl & Hcml & HknM & #HmRFrag & HmRFull & #HmTfrag & #HdomR & #HmsgRres
             & HknRes & %Hser & HmvalRes & Hres)".
    wp_lam. rewrite Hskt. wp_pures.
    assert (∃ γs', γM !! (m_sender m) = Some γs') as (γs' & Hmγs).
    { assert (is_Some (γM !! (m_sender m))).
      { apply elem_of_dom. by rewrite Hdom. }
      naive_solver. }
    iDestruct "HmvalRes" as "[#HlRes|#HrRes]"; last first.
    (* ===================================================================== *)
    (* Case 1. The message is ACKID or MSGID. (Absurd). *)
    (* ===================================================================== *)
    { iDestruct "HrRes" as "((%γ & #Habs1) & _)".
    iDestruct (big_sepM_lookup_acc _ cM (m_sender m) _ Hsm with "[$HknRes]")
      as "(HchanRes & HknResAcc)".
    iDestruct "HchanRes" as (γs0 ck0) "((#Htk0 & HCkF & %Hhst1 & %Hhst2) & HchanRes)".
    iDestruct "HchanRes" as "[(%H1 & Habs2 & Hc1 & Hc2)|HchanRes]"; last first.
    { iDestruct "HchanRes" as (γc c sidLB_l sidLB_n ackId_l ackId_n) "HchanRes".
      iDestruct "HchanRes"
        as "(%Hhst3 & %Hhst4 & %Hchan & Hsmode & Hckf & HsL & HaL & #Hmono & #Hpers)".
      naive_solver. }
    { iDestruct "Habs1" as "(Hγ1 & Habs1)".
      iDestruct "Habs2" as "(Hγ2 & Habs2)".
      iDestruct (session_token_agree with "[$Hγ1] [$Hγ2]") as "->".
      by iDestruct (SM_opened_excl with "[$Habs2] [$Habs1]") as "%". } }
    (* ===================================================================== *)
    (* Case 2. The message is INIT or COOKIE *)
    (* ===================================================================== *)
    (* We proceed by case analysis on the shape of the received message's value. *)
    iDestruct "HlRes" as (s i ->) "Hinit".
    wp_pures.
    iDestruct "Hinit" as "[(-> & ->) |(-> & %γs & #Htk)]".
    (* ----------------------------------------------------------------- *)
    (* Case 2.1: INIT message. *)
    (* ----------------------------------------------------------------- *)
    case_bool_decide as Hseq; first done.
    (* Resend the INIT-ACK for free. *)
    { wp_pures.
      wp_apply (s_ser_spec (msg_serialization RCParams_srv_ser)).
      { eauto. iPureIntro. apply (serInit "INIT-ACK" cookie Right). }
      iIntros (s1 Hs1). wp_pures.
      iDestruct (big_sepM_lookup_acc _ cM (m_sender m) _ Hsm with "[$HknRes]")
        as "(HchanRes & HknResAcc)".
      iDestruct "HchanRes" as (γs0 ck0) "((#Htk0 & HCkF & %Hhst1 & %Hhst2) & HchanRes)".
      iDestruct "HchanRes" as "[(%H1 & Hsmode & Hc1 & Hc2)|HchanRes]"; last first.
      { iDestruct "HchanRes" as (γc c sidLB_l sidLB_n ackId_l ackId_n) "HchanRes".
        iDestruct "HchanRes"
          as "(%Hhst3 & %Hhst4 & %Hchan & Hsmode & Hckf & HsL & HaL & #Hmono & #Hpers)".
        naive_solver. }
      destruct Hhst2 as (mm & mv & Hm & Hmser & Hmdest & Hmsend & Hmval).
      assert (m_body mm = s1) as Hmbdy_eq.
      { subst. apply (msg_ser_is_ser_injective_alt Right _ _ (InjLV (#"INIT-ACK", #cookie ))).
        naive_solver. naive_solver. }
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
      simpl in *.
      assert (mt = mm) as Heqmm.
      { rewrite /mt. rewrite -Hmbdy_eq. destruct mm. simpl. simplify_eq /=. f_equal. }
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
      iAssert (⌜m ∈ R0⌝)%I as "%HinR0".
      { destruct (bool_decide (m ∈ R0)) eqn:HmR0.
        - by apply bool_decide_eq_true_1 in HmR0.
        - apply bool_decide_eq_false_1 in HmR0.
          destruct Hhst1
            as (minit & vinit & Hinit & Hmserinit & Hmdestinit & Hmsendinit & Hmvalinit).
          assert (m_body minit = m_body m) as Hmbdy_eqinit.
          { subst. simpl in *.
            by apply (msg_ser_is_ser_injective_alt Left _ _ (InjLV (#"INIT", #0))). }
          assert (m = minit).
          { destruct m, minit. by simpl in *; subst. }
          set_solver. }
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
        iExists γs0, ck0.
        iSplitL "HCkF".
        { iFrame; eauto. }
        iLeft. iFrame; eauto. }
      iFrame "#∗".
      iExists _, _. iFrame; eauto. }
    (* ----------------------------------------------------------------- *)
    (* Case 2.2: COOKIE message. *)
    (* ----------------------------------------------------------------- *)
    wp_pures.
    (* We proceed by case analysis on whether m is in R0. *)
    destruct (bool_decide (m ∈ R0)) eqn:Hm.
    (* ----------------------------------------------------------------- *)
    (* Case 2.2.1. We show that m ∈ R0 is absurd. *)
    (* ----------------------------------------------------------------- *)
    { apply bool_decide_eq_true_1 in Hm.
       iDestruct (big_sepS_elem_of _ R0 m Hm with "HmsgRres") as "Hmsgres".
       iDestruct "Hmsgres"
         as (γs0 mval0 n0 Hser0)
              "(#Htk0 & [#(%Hl & %Hl2) | (%x & %y & %Habs1 & %Habs2)])";
         [| naive_solver].
       rewrite Hl in Hser0.
       simpl in *.
       assert ((InjLV (#"COOKIE", #i)) = (InjLV (#"INIT", #0))) as Habs.
       { apply (msg_ser_is_ser_injective Left (m_body m) _ _);
           subst; naive_solver. }
       naive_solver. }
    (* ----------------------------------------------------------------- *)
    (* Case 2.2.2. We know now that m is not in R0. *)
    (* ----------------------------------------------------------------- *)
    (* Now we know that the cookie message is fresh, so that
       - either the cookie number is wrong, in which case we show the absurdity
       - or it matches the cookie number, and then we need
         to change the state to established connection. *)
    apply bool_decide_eq_false_1 in Hm.
    (* Get the cookie resource. *)
    iDestruct "Hres" as "[%Habs|Hck]"; first done.
    iDestruct "Hck" as (mvalA HserA) "(#Hcsi' & Hck)".
    iDestruct "Hck" as "[Hck|Hck]"; last first.
    iAssert (∃ mvalr, ⌜mvalA = InjRV mvalr⌝)%I as (mvalr) "%Hmvalr".
    { iDestruct "Hck" as "(_ & [(%a & -> & _)|(%_ & %z & -> & _)])"; eauto. }
    rewrite Hmvalr in HserA.
    assert ((InjLV (#"COOKIE", #i)) = (InjRV mvalr)) as Habs.
    { apply (msg_ser_is_ser_injective Left (m_body m) _ _);
          subst; naive_solver. }
    naive_solver.
    iDestruct "Hck" as (s0 r0 i0 -> n Hn) "Hck".
    apply (msg_ser_is_ser_injective Left (m_body m) _ _ HserA) in Hser.
    inversion Hser. subst.
    iDestruct "Hck" as "[(%Habs & Hck)|(_ & _ & Hck & _)]";
      first naive_solver.
    case_bool_decide as Hckeq; last first.
    (* ----------------------------------------------------------------- *)
    (* Case 2.2.2.2: The COOKIE number number does not match *)
    (* ----------------------------------------------------------------- *)
    (* The absurd case: we will use the agreement (frac_auth_agree_L) on
       CookieRes clt_addr i * CookieFull ck to show that i = ck. *)
    { wp_pures.
      iDestruct (big_sepM_lookup_acc _ cM (m_sender m) _ Hsm with "[$HknRes]")
        as "(HchanRes & HknResAcc)".
      iDestruct "HchanRes" as (γs0 ck0) "((#Htk0 & HCkF & %Hhst1 & %Hhst2) & HchanRes)".
      iDestruct "HchanRes" as "[(%H1 & Habs2 & Hc1 & Hc2)|HchanRes]"; last first.
      { iDestruct "HchanRes" as (γc c sidLB_l sidLB_n ackId_l ackId_n) "HchanRes".
        iDestruct "HchanRes"
          as "(%Hhst3 & %Hhst4 & %Hchan & Hsmode & Hckf & HsL & HaL & #Hmono & #Hpers)".
        naive_solver. }
      iDestruct (CookieRes_Full_valid with "[$HCkF] [$Hck]") as "%Habs".
      naive_solver. }
    (* ----------------------------------------------------------------- *)
    (* Case 2.2.2.1: The COOKIE number matches.   *)
    (* ----------------------------------------------------------------- *)
    (* Changing the state by creating a new channel descriptor.  *)
    { wp_pures.
      wp_alloc lLB as "(HsidLB1 & HsidLB2)".
      wp_alloc lAD as "(Hackid1 & Hackid2)".
      wp_pures.
      assert (cM = <[(m_sender m):=(HalfOpened cookie)]>(delete (m_sender m) cM))
        as Hidel.
      { rewrite insert_delete; eauto. }
      rewrite {2} Hidel.
      assert ((delete (m_sender m) cM) =
                (delete (m_sender m) (delete (m_sender m) cM))) as Hdeldel.
      { by rewrite delete_idemp. }
      iPoseProof big_sepM_insert_delete as "(Hextract & _)".
      iDestruct ("Hextract" with "[$HknRes]") as "(HchanRes & HknResAcc)".
      rewrite -Hdeldel.
      iDestruct "HchanRes" as (γs0 ck0) "((#Htk0 & HCkF & %Hhst1 & %Hhst2) & HchanRes)".
      iDestruct "HchanRes" as "[(%H1 & Habs2 & Hc1 & Hc2)|HchanRes]"; last first.
      { iDestruct "HchanRes" as (γc c sidLB_l sidLB_n ackId_l ackId_n) "HchanRes".
        iDestruct "HchanRes"
          as "(%Hhst3 & %Hhst4 & %Hchan & Hsmode & Hckf & HsL & HaL & #Hmono & #Hpers)".
        naive_solver. }
      iDestruct (session_token_agree with "[$Htk0][$Htk]") as "->".
      wp_apply
        (make_new_channel_descr_spec γs (m_sender m) (iProto_dual RCParams_protocol) Right lAD lLB
          with "[$HsidLB1 $Hackid1 $Hc2]"); [done|done|done | ].
      iIntros (γe c) "(#HaT & #HsT & #HlT & Hchan)". simpl in *.
      wp_pures.
      (* Unfolding the definition to get the persistent knowledge(send/recv locks, etc.) *)
      rewrite{1} /iProto_mapsto seal_eq /iProto_mapsto_def.
      iDestruct "Hchan" as
        (γs'' sd ser serf sa dst sbuf slk rbuf rlk )
          "(%sidLBLoc & %ackIdLoc & %sidx & %ridx & Hhy)".
      iDestruct "Hhy"
        as "(%Hc & %Heqc & %Heqg & Hl & %Hlser & Hmn1 & Hmn2
                 & #Hst' & #HaT' & #HsT' & #HlT'
                 & Hpown & #Hslk & #Hrlk)".
      simpl. destruct sd as [|].
      - by iDestruct (ChannelSideToken_agree with "[$HsT] [$HsT']") as "%".
      - simpl in *.
        iDestruct (ChannelIdxsToken_agree with "[$HlT] [$HlT']") as "%Heql".
        inversion Heql as ((Heql1 & Heql2)).
        iDestruct (ChannelAddrToken_agree with "[$HaT] [$HaT']") as "%Heqa".
        inversion Heqa as ((Heqa1 & Heqa2)).
        iDestruct (session_token_agree with "[$Htk0] [$Hst']") as "->".
      (* Updating the ghost resources. *)
        iApply fupd_aneris_wp.
        iDestruct "Habs2" as "(#Htk2 & Hsmoderes)".
        iMod (SM_own_update with "[$Hsmoderes]") as "#Hopened".
        iModIntro.
        wp_apply (aneris_wp_fork with "[-]").
        iSplitL.
        + iNext. wp_pures.
          wp_load. wp_pures.
          wp_apply (@wp_map_insert
                      _ _ _ _ _ _ Inject_socket_address _
                      Inject_conn_state srv_ip ( (m_sender m))
                      ( (Connected ((c, cookie), (sidLBLoc, ackIdLoc)))) cmv cM $! Hmap).
          iIntros (cmv' Hmap').
          wp_store.
          wp_pures.
          wp_apply (s_ser_spec (msg_serialization RCParams_srv_ser)).
          { eauto. iPureIntro. apply (serInit _ 0 Right). }
          iIntros (s1 Hs1). wp_pures.
          iAssert (mono_nat.mono_nat_lb_own (session_clt_idx_name γs'') 0) as "#Hmono".
          { rewrite /can_init. simpl.
            iDestruct "Hc1" as "(_ & Hmono & _)".
            by iApply mono_nat.mono_nat_lb_own_get. }
          (* Sending "COOKIE-ACK, cookie" back. *)
          wp_bind (SendTo _ _ _).
          iInv (RCParams_srv_N.@"skt")
                 as (R' T')
                      "(>Hh & >Hmh & >#HmRfrag & >HmTauth & #HmR')".
          wp_apply (aneris_wp_send srv_ip
                     with "[$Hh $Hmh Hc1]"); [done|done|  | ].
          { iSplit; iNext; first done. inversion Hckeq as (Hseqv).
            iExists (InjLV (#"COOKIE-ACK", #0)).
            do 2 (iSplit; first done).
            iLeft.
            iExists _, _.
            iSplit; first done.
            iExists 0, γs''. simpl.
            iSplit; first done.
            iSplit; first eauto.
            iRight. iSplit; first done.
            iExists γs''. iSplit; last by iFrame "Htk2 Hopened".
            by iFrame. }
          iIntros "(Hh & Hmh)".
          set (resp := {|
                        m_sender := RCParams_srv_saddr;
                        m_destination := m_sender m;
                        m_body := s1
                      |}).
          iDestruct "HmTauth" as (T00 HsubT00) "HmTauth".
          iAssert (⌜T0 ⊆ T00⌝)%I as "%HmhrRel".
          {  iDestruct (own_valid_2 with "HmTauth HmTfrag")
              as %[Hv1%gset_included Hv2]%auth_both_valid_discrete.
             iPureIntro. set_solver. }
          iMod (own_update _ _ ((● ({[resp]} ∪ T00)) ⋅ (◯ ({[resp]} ∪ T00)))
                 with "HmTauth")
            as "[HmTauth #HTfrag]".
          { apply auth_update_alloc. apply gset_local_update. set_solver. }
          iSplitL "Hh Hmh HmTauth".
          { iModIntro. iNext. iExists R', ({[resp]} ∪ T').
            iFrame; eauto. iSplit; first eauto. iSplitL; last done.
            iExists ({[resp]} ∪ T00). eauto with set_solver. }
          iModIntro.
          wp_pures.
          wp_apply (acquire_spec with "Hqlk").
          iIntros (qv) "(-> & Hlkd & Hqres)".
          iDestruct "Hqres" as (qv vs) "(Hql & %Hisq & Hqres)".
          wp_seq.
          wp_load.
          wp_pures.
          wp_apply (@wp_queue_add _ _ _ _ _ vs qv (c, #(m_sender m))%V srv_ip $! Hisq).
          iIntros (rv Hqrv).
          wp_store.
          (* Release the lock by providing the channel mapsto. *)
          wp_apply (release_spec srv_ip γqlk qlk (conn_queue_lock_def cql)
                     with "[Hlkd Hql Hqres Hmn1 Hmn2 Hpown Hl]").
          { iFrame "Hlkd Hqlk".
            iExists rv, (vs ++ [(c, #(m_sender m))%V]).
            iFrame "Hql".
            iSplit; first done.
            iApply (big_sepL_snoc with "[$Hqres Hmn1 Hmn2 Hpown Hl]").
            iExists γe, c, (m_sender m).
            iSplit; first done.
            iFrame "#".
            rewrite{1} /iProto_mapsto seal_eq /iProto_mapsto_def.
            iExists _, _, _, _, _, _, _.
            iExists _, _, _, _, _, _, _.
            iFrame "Hslk Hrlk HsT HaT Hmn1 Hmn2 Hpown Hl".
            iFrame "#∗".
            subst; eauto. }
          iIntros (? ->).
          wp_pures. iApply "HΦ".
          iSplit; first done.
          (* Restore the loop invariant. *)
          iExists _, _, _, _, _, _.
          iSplit; first done.
          iFrame "Hskl".
          iSplitL.
          { iExists ({[m]} ∪ R0), ({[resp]} ∪ T00), cmv', γM.
            iExists (<[m_sender m:=Connected (c, cookie, (sidLBLoc, ackIdLoc))]> cM).
            iSplit; first done.
            iFrame "#∗".
            iSplit.
            { iPureIntro. rewrite Hdom. set_solver. }
            iSplit.
            { iApply (big_sepS_insert with "[$HdomR]"); first done.
              iPureIntro. rewrite Hdom. set_solver.  }
            iSplit.
            { iApply (big_sepS_insert with "[HmsgRres]"); first done.
              iSplit.
              - iExists γs'', (InjLV (#"COOKIE", #n)), n.
                iSplit; first done.
                iFrame "Htk0".
                iRight.
                iExists c, sidLBLoc, ackIdLoc.
                rewrite lookup_insert. naive_solver.
              - iApply (big_sepS_mono _ _ _ with "HmsgRres").
                iIntros (m0 Hm0) "#Hres".
                destruct (bool_decide (m_sender m = m_sender m0)) eqn:Hmeq.
                + apply bool_decide_eq_true_1 in Hmeq.
                  iDestruct "Hres"
                    as (γs0 mval0 n0 Hser0) "(#Htk0 & [#(%Hl & %Hl2) | #Hr])".
                  ++ rewrite Hmeq. rewrite -Hmeq in Hl2.
                     iExists γs0, (InjLV (#"INIT", #0)), n.
                     iSplit; first (subst; done).
                     iFrame "Htk0".
                     iRight.
                     iExists c, sidLBLoc, ackIdLoc.
                     rewrite lookup_insert. naive_solver.
                  ++ iDestruct "Hr" as (???) "%Habs".
                     rewrite -Hmeq in Habs. naive_solver.
                + apply bool_decide_eq_false_1 in Hmeq.
                  iDestruct "Hres"
                    as (γs0 mval0 n0 Hser0) "(#Htk0 & [#(%Hl & %Hl2) | #Hr])".
                  * iExists γs0, _, _. iFrame "#∗". iSplit; first done.
                    iLeft. by rewrite lookup_insert_ne.
                  * iDestruct "Hr" as (???) "%Habs".
                    iExists γs0, _, n0. iFrame "#∗". iSplit; first done.
                    iRight. rewrite lookup_insert_ne; subst; eauto. }
            iApply big_sepM_insert_delete.
            iSplitR "HknResAcc".
            assert (n = ck0) as -> by naive_solver.
            assert (ck0 = cookie) as -> by naive_solver.
            {  iExists γs'', cookie. iFrame "HCkF".
               iSplitR.
               { iSplit; first done.
                 destruct Hhst1 as (y0 & ? & ? & ? & ?).
                 destruct Hhst2 as (y1 & ? & ? & ? & ?).
                 iSplit.
                 { simpl in *. subst.
                   iExists y0, _; eauto with set_solver. }
                 iExists y1, _; eauto with set_solver. }
               iRight.
               iExists γe, c, _, 0, _, 0.
               iFrame "HsidLB2 Hackid2 Hck Hmono".
               iSplit.
               { iExists m, _. iPureIntro.
                 split; first by set_solver.
                 split_and!; eauto. }
               iSplit.
               { iExists resp, _. iPureIntro.
                 split; first by set_solver.
                 split_and!; eauto. }
               iSplit; first done.
               iSplit; first by iFrame "#".
               subst; eauto.
               iExists _, _, _, _, _, _.
               iExists _, _. iFrame "#∗".
               iPureIntro; split_and!; eauto. }
            iApply (big_sepM_mono with "[$HknResAcc]").
            iIntros (k x Hkx) "HchanRes".
            destruct (bool_decide (m_sender m = k)) eqn:Hkm.
            - apply bool_decide_eq_true_1 in Hkm.
              rewrite -Hkm in Hkx. by rewrite lookup_delete in Hkx.
            - apply bool_decide_eq_false_1 in Hkm.
              rewrite lookup_delete_ne in Hkx; last done.
              iDestruct "HchanRes" as (γi cki) "((#Htk0i & HCkFi & %Hhst1i & %Hhst2i) & HchanRes)".
              iDestruct "HchanRes" as "[(%Hb & Hsmode' & Hc1 & Hc2)|HchanRes]"; last first.
              { iExists γi, cki. iFrame "HCkFi Htk0i".
                simpl in *.
                iSplitR.
                destruct Hhst1i as (y0 & ? & ? & ? & ?).
                destruct Hhst2i as (y1 & ? & ? & ? & ?).
                iSplit.
                { simpl in *. subst.
                  iExists y0, _; eauto with set_solver. }
                iExists y1, _; eauto with set_solver.
                iDestruct "HchanRes" as (γc' c' sidLB_l' sidLB_n' ackId_l' ackId_n') "HchanRes".
                iDestruct "HchanRes"
                  as "(%Hhst3i & %Hhst4i & %Hchan' & #Hopened & Hckf & HsL & HaL & #Hmono & #Hpers)".
                iDestruct "Hpers" as
                  (γsi ser' serf' sa' sbuf' slk' rbuf' rlk' Hc') "Hpers".
                iDestruct "Hpers"
                  as "(%Hgeq' & %Hgleq' & Htk' & HcT & HaT & HiT & Hslk & Hrlk)".
                iRight.
                destruct Hhst3i as (y3 & ? & ? & ? & ? & ? & ?).
                destruct Hhst4i as (y4 & ? & ? & ? & ? & ? & ?).
                subst.
                iExists γc', _, _, _, _, _.
                iFrame "HsL HaL Hckf".
                iSplit.
                { iExists y3, (InjLV (#"COOKIE", #cki)). by eauto with set_solver. }
                iSplit.
                { iExists y4, _. by eauto with set_solver. }
                iSplit; first done.
                subst.
                iSplit.
                { iDestruct "Hopened" as "(H1 & H2)". iFrame "#". }
                iFrame "#".
                iExists _, _, _, _, _, _, _, _. iFrame "#"; eauto. }
              iExists γi, cki. iSplitL "HCkFi". iFrame "#∗".
              destruct Hhst1i as (y0 & ? & ? & ? & ?).
              destruct Hhst2i as (y1 & ? & ? & ? & ?).
              iSplit.
              { simpl in *. subst.
                iExists y0, _; eauto with set_solver. }
              iExists y1, _; eauto with set_solver.
              iLeft; first by iFrame. }
          iFrame "Hqlk".
          iExists _, _. subst; eauto.
        + iNext.
          simplify_eq.
          iApply (send_from_chan_loop_spec
                  (RCParams_srv_N.@"skt") _ _ _ _ _ _ _ _ Right with "[-]");
          [done|done|done|done|done|iSplitL; eauto with iFrame|done].
          iExists _, _; subst; eauto.
          iFrame "#∗". iExists γs''. simpl. iFrame "#". }
  Qed.

End Proof_of_server_conn_step_2.
