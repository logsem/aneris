From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants mono_nat.
From aneris.aneris_lang Require Import ast tactics.
From iris.algebra.lib Require Import excl_auth.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_proof.
From aneris.aneris_lang.lib Require Import pers_socket_proto lock_proof queue_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.resources Require Import
     chan_endpoints_resources
     socket_interp.
From aneris.examples.reliable_communication.proof.common_protocol Require Import
     proof_of_make_new_channel_descr
     proof_of_send_from_chan_loop.
From aneris.examples.reliable_communication.proof.client Require Import
     proof_of_make_client_skt
     proof_of_connect_step_1
     proof_of_connect_step_2
     proof_of_client_recv_on_chan_loop
     client_resources.

Section Proof_of_connect.
  Context `{!anerisG Mdl Σ,
            !Reliable_communication_service_params,
            !chanG Σ,
            !lockG Σ}.
  Context `{!server_ghost_names}.


  Lemma connect_internal_spec (skt : val) (clt_addr : socket_address) :
    {{{ ∃ h s, isClientSocketInternal skt h s clt_addr true ∅ ∅}}}
      connect skt #RCParams_srv_saddr @[ip_of_address clt_addr]
      {{{ γe c, RET c;
          c ↣{ γe, ip_of_address clt_addr, RCParams_clt_ser} RCParams_protocol ∗
            ChannelAddrToken γe (clt_addr, RCParams_srv_saddr) }}}.
  Proof.
    iIntros (Φ) "HisClt HΦ".
    wp_lam. wp_let.
    rewrite /isClientSocketInternal /isSocket /is_skt_val /=.
    iDestruct "HisClt" as (h s) "(#Hsrv_si & HisClt & (Hmh & #HmhR))".
    iDestruct "HisClt" as (-> Hsaddr Hsblock) "(Hh & #Hsi)".
    wp_pures.
    wp_apply (aneris_wp_rcvtimeo_unblock with "[$Hh]"); eauto with lia.
    iIntros "Hh". wp_pures.
    wp_apply (client_conn_step_1_spec _ _ _ clt_addr ∅ ∅ with "[$Hh $Hmh] [HΦ]").
    { rewrite /isClientSocketInternal /isSocket /is_skt_val /=.
      iSplitL. { iFrame "#∗"; eauto. }
      iSplitL. { iIntros (? ? ? ? ?); naive_solver. }
      iSplitL. { iIntros (? ? ? ? ?); naive_solver. }
      iLeft. do 3 (iSplit; first eauto).
      iIntros (m) "Hm".
      iDestruct "Hm" as (cookie γs Hser Hsrc) "(%Hdst & #Htk & Hcookie)".
      iExists (InjLV (#(LitString "INIT-ACK"), #(LitInt cookie))%V).
      do 2 (iSplit; first eauto).
      iLeft.
      iExists "INIT-ACK", cookie. iSplit; first eauto.
      rewrite /client_init_interp. eauto. iExists cookie.
      iExists γs; iSplit; first done. subst; eauto. }
    iNext.
    iIntros (v1) "HconnPost".
    iDestruct "HconnPost" as (R T) "HconnPost".
    iDestruct "HconnPost"
      as (n1 m1 mt)
           "(%Hn & %Hm & (%Hser1 & %Hdst & HisClt & Hpost & Hcnd2 & _ & _))".
    iDestruct "HisClt" as "(_ & HisClt & Hmh1 & #HmhR1)".
    iDestruct "HisClt" as (-> Hsaddr1 Hsblock1) "(Hh1 & _)".
    wp_pures.
    rewrite Hn.
    set (skt := ((#(LitSocket h),
                     (side_elim Left
                        (s_ser (s_serializer (msg_serialization RCParams_clt_ser)))
                        (s_ser (s_serializer (msg_serialization RCParams_srv_ser))),
                     side_elim Left
                       (s_deser (s_serializer (msg_serialization RCParams_srv_ser)))
                       (s_deser (s_serializer (msg_serialization RCParams_clt_ser)))),
                       s_ser (s_serializer RCParams_clt_ser)))%V).
    wp_apply (client_conn_step_2_spec skt _ _ clt_addr R _ n1
               with "[$Hh1 $Hmh1 Hpost $Hcnd2] [HΦ]").
    { rewrite /isClientSocketInternal /isSocket /is_skt_val /=.
      iDestruct "Hpost" as "(%γs & #Htk & Hck)".
      iSplitR. { iFrame "#∗"; eauto. }
      iRight. iSplit; first done. iFrame.
      iSplit; first done.
      iSplitL; [by iExists _; iFrame|].
      iSplit; [by iExists _; iFrame|].
      iIntros (m n) "Hm".
      iDestruct "Hm" as (γs' Hser Hsrc Hdest) "(#Htk' & #Hsmode & Hcan_init)".
      iExists (InjLV (#(LitString "COOKIE-ACK"), #(LitInt n))%V).
      do 2 (iSplit; first eauto).
      iLeft. iExists _, _. iSplit; first eauto.
      rewrite /client_init_interp. iExists n%nat.
      iExists γs'. iSplit; first done. rewrite Hdest.
      iSplit; first eauto.
      iRight.
      iSplit; first done.
      iExists _. eauto; iFrame "#∗". }
    iNext. iIntros (v2) "HconnPost".
    iDestruct "HconnPost" as (R2 T2) "HconnPost".
    iDestruct "HconnPost"
       as (m2 n2 mt2) "(-> & HconnPost)".
    iDestruct "HconnPost" as "(%Hm2 & %Hser2 & %Hdst2 & HisClt & (%γ & Hres) & _)".
     iDestruct "HisClt" as "(#Hsrv_si2 & HisClt & (Hmh & #HmhR2))".
    iDestruct "HisClt" as (? Hsaddr2 Hsblock2) "(Hh & #Hsi2)".
    wp_pures.
    wp_apply (aneris_wp_rcvtimeo_block with "[$Hh]"); eauto with lia.
    iIntros "Hh". wp_pures. rewrite Hdst2.
    wp_alloc lLB as "(HsidLB1 & HsidLB2)".
    wp_alloc lAD as "(Hackid1 & Hackid2)".
    wp_pures.
    set (sock := {| saddress := saddress s; sblock := true |}).
    iMod ((inv_alloc
             (chan_N (session_chan_name γ))
            _ (socket_inv_def h clt_addr sock Left))
           with "[Hh Hmh]") as "#Hsock_inv".
    { iNext. iExists _, _. iFrame "#∗". }
    iAssert (socket_resource skt clt_addr (chan_N (session_chan_name γ)) Left) as "#Hsinv".
    { iFrame "#∗". iExists h, sock; eauto. }
    iAssert (session_token clt_addr γ) as "#Hst".
    { rewrite /can_init. by iDestruct "Hres" as "((#Hs & _) & _)". }
    iAssert (mono_nat_lb_own
     (side_elim Left (session_srv_idx_name γ) (session_clt_idx_name γ))
     0) as "#Hmono".
    { rewrite /can_init. simpl. by iDestruct "Hres" as "((_ & _ & Hm & _) & _)". }
    iDestruct "Hres" as "(Hres & #Hsmode)".
    wp_apply
      (make_new_channel_descr_spec γ _ _ Left lAD lLB _ with "[$Hres $HsidLB1 $Hackid1]");
      [done|done|done | ].
    iIntros (γe c) "(#HaT & #HsT & #HlT & Hchan)". wp_pures.
    rewrite{2} /iProto_mapsto seal_eq /iProto_mapsto_def.
    iDestruct "Hchan" as
      (γs sd serl serf sa dst sbuf slk rbuf rlk )
        "(%sidLBLoc & %ackIdLoc & %sidx & %ridx & Hhy)".
    iDestruct "Hhy"
      as "(%Hc & %Heqc & %Heqg & Hserl & %Hserl & Hmn1 & Hmn2
               & #Hst' & #HaT' & #HsT' & #HlT'
               & Hpown & #Hslk & #Hrlk)".
    simpl. destruct sd as [|]; last first.
    { by iDestruct (ChannelSideToken_agree with "[$HsT] [$HsT']") as "%". }
    simpl in *.
    iDestruct (ChannelIdxsToken_agree with "[$HlT] [$HlT']") as "%Heql".
    inversion Heql as ((Heql1 & Heql2)).
    iDestruct (ChannelAddrToken_agree with "[$HaT] [$HaT']") as "%Heqa".
    inversion Heqa as ((Heqa1 & Heqa2)).
    iDestruct (session_token_agree with "[$Hst] [$Hst']") as "->".
    wp_apply (aneris_wp_fork with "[-]").
    iSplitL.
    - iNext. wp_pures.
      wp_apply (aneris_wp_fork with "[-]").
      iSplitR "HsidLB2 Hackid2".
      + iNext; wp_seq; iApply "HΦ"; iFrame "#∗".
        rewrite{1} /iProto_mapsto seal_eq /iProto_mapsto_def.
        iExists _, Left, _, _, _, _, _, _.
        iExists _, _, _, _, _, _.
        simpl. iFrame "#∗"; eauto.
      + replace (LitInt (Z.of_nat 0)) with (LitInt 0) by eauto with lia.
        simpl in *.
        iApply (client_recv_on_chan_loop_spec
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 0
                 with "[$Hsinv $Hst $Hslk $Hrlk $HsidLB2 $Hackid2]"); eauto.
    - simpl. simplify_eq.
      iApply (send_from_chan_loop_spec
                (chan_N (session_chan_name γs)) _ _ _ _ _ _ _ _ Left with "[-]");
        [done|done|done|done|done|iSplitL; eauto with iFrame|done].
  Qed.

End Proof_of_connect.
