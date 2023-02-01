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
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.resources Require Import
     chan_session_resources socket_interp.
From aneris.examples.reliable_communication.proof.server Require Import
     server_resources.

Section Proof_of_server_conn_step_1.
  Context `{!anerisG Mdl Σ}.
  Context `{!Reliable_communication_service_params}.
  Context `{!chanG Σ, !lockG Σ}.
  Context `{!server_ghost_names}.

  Notation srv_ip := (ip_of_address RCParams_srv_saddr).

  Lemma server_conn_step_to_open_new_conn_spec
      (skl : loc) (skt_passive : val) skt sock h (cml : loc) cmv (cql : loc) qlk γqlk mval m
       (cM :gmap socket_address conn_state)  (γM : session_names_map) (R T : gset message) :
    skt_passive = (skt, #cml, (#cql, qlk))%V →
    dom γM = dom cM →
    m_sender m ∉ dom cM →
    cM !! m_sender m = None →
    is_map cmv cM →
    m_destination m = RCParams_srv_saddr →
    saddress sock = Some RCParams_srv_saddr →
    sblock sock = true →
    {{{ is_skt_val skt h Right ∗
        is_conn_queue_lock γqlk qlk cql ∗
        RCParams_srv_saddr ⤇ server_interp ∗
        m_sender m ⤇ client_interp ∗
        inv Nskt (socket_inv_def h RCParams_srv_saddr sock Right) ∗
        skl ↦[srv_ip]{1 / 3} InjRV (#cql, qlk) ∗
        cml ↦[srv_ip] cmv ∗
        known_sessions γM ∗
        own γ_srv_known_messages_R_name (● ({[m]} ∪ R)) ∗
        own γ_srv_known_messages_T_name (◯ T) ∗
        ([∗ set] m ∈ R, ⌜(m_sender m) ∈ dom γM⌝) ∗
        ([∗ set] m ∈ R, message_conn_map_resources cM m) ∗
        ([∗ map] sa↦st ∈ cM, session_map_resources sa st R T) ∗
        ⌜s_is_ser (msg_serialization RCParams_clt_ser) mval (m_body m)⌝ ∗
        ((∃ (s r : string) (i : Z), ⌜mval = InjLV (#s, #i)⌝ ∗
                   (∃ n : nat, ⌜Z.of_nat n = i⌝ ∗ server_init_interp (m_sender m) s r n))
                ∨ (∃ γs : session_name, session_connected (m_sender m) γs) ∗
                ((∃ ackid : val, ⌜mval = InjRV (InjLV ackid)⌝ ∗
                    (∃ n : nat, ⌜ackid = #n⌝ ∗ ack_interp_pers (m_sender m) n Right))
                 ∨ (∃ (i : Z) (w : val), ⌜mval = InjRV (InjRV (#i, w))⌝ ∗
                      (∃ n : nat, ⌜Z.of_nat n = i⌝ ∗ idmsg_interp_pers (m_sender m) n w Right))))
    }}}
      server_conn_step_to_open_new_conn
      (skt, #cml, (#cql, qlk))%V mval #(m_sender m) @[srv_ip]
   {{{ v, RET v; ⌜v = #()⌝ ∗ isServer_listening_loop_resources skt_passive }}}.
  Proof.
    iIntros (Hsrv_skt Hdom Hdomc Hsm Hmap Hdest Hsaddr Hsblk Φ).
    iIntros "(%Hskt & #Hqlk & #Hsi & #Hcsi & #Hsinv & Hspat) HΦ".
    iDestruct "Hspat" as
      "(Hskl & Hcml & HknM & HmFull & #HmTfrag & #HdomR & #HmsgRres & HknRes & %Hser & HmvalRes)".
    wp_lam. rewrite Hskt. wp_pures.
    iDestruct "HmvalRes" as "[HlRes|HrRes]".
    - iDestruct "HlRes" as (s r i ->) "(%n & %Hn & HRes)". wp_pures.
      case_bool_decide as Hseq. wp_pures.
      -- case_bool_decide as Hargeq.
         (* The message is (INIT,0). *)
         --- wp_pures.
             (* Creating the session opening ghost and physical resources. *)
             wp_apply aneris_wp_lb_get. iIntros "Hstep".
             wp_apply aneris_wp_rand; first by iPureIntro; lia.
             iIntros (ck) "(%Hck1 & %Hck2)".
             pose (ckn := Z.to_nat ck).
             replace ck with (Z.of_nat ckn); last by lia.
             wp_apply fupd_aneris_wp.
             iMod (session_map_update _ _ RCParams_protocol ckn (nroot : namespace) (⊤ :coPset)
                    with "[] [$HknM] [$Hstep]") as "HupdRes";
               [ by rewrite -Hdom in Hdomc |].
             iModIntro.
             iDestruct "HupdRes"
               as (γs) "(HknM & #Hstk & Hhopened & HckF & HckRes & HcanInit1 & HcanInit2)".
             wp_let. wp_load. wp_pures.
             wp_apply (@wp_map_insert
                         _ _ _ _ _ _
                         Inject_socket_address _ Inject_conn_state srv_ip
                         (m_sender m) ((HalfOpened ckn))); [ iPureIntro; by apply Hmap|].
             iIntros (cmv' Hcmv').
             wp_store.
             wp_pures.
               wp_apply (s_ser_spec (msg_serialization RCParams_srv_ser)).
               { eauto. iPureIntro. apply (serInit _ ckn Right). }
               iIntros (s1 Hs1). wp_pures.
               (* Sending "INIT-ACK, cookie" back. *)
               wp_bind (SendTo _ _ _).
               iInv Nskt
                 as (R' T')
                      "(>Hh & >Hmh & >#HmRfrag & >HmTauth & #HmR')".
               wp_apply (aneris_wp_send srv_ip
                          with "[$Hh $Hmh HRes HckRes]"); [done|done|  | ].
               { iSplit; iNext; first done. inversion Hseq as (Hseqv).
                 iDestruct "HRes" as "[(_ & -> & -> & HRes)|(%Habs & _)]"; last done.
                 iApply "HRes".
                 iExists ckn, γs.
                 do 3 (iSplit; first done).
                 eauto with iFrame. }
               iIntros "(Hh & Hmh)".
               set (resp := {|
                           m_sender := RCParams_srv_saddr;
                           m_destination := m_sender m;
                           m_body := s1
                         |}).
               iDestruct "HmTauth" as (T0 HsubT0) "HmTauth".
                iAssert (⌜T ⊆ T0⌝)%I as "%HmhrRel".
                {  iDestruct (own_valid_2 with "HmTauth HmTfrag")
                    as %[Hv1%gset_included Hv2]%auth_both_valid_discrete.
                   iPureIntro. set_solver. }
               iMod (own_update _ _ ((● ({[resp]} ∪ T0)) ⋅ (◯ ({[resp]} ∪ T0))) with "HmTauth")
                 as "[HmTauth #HTfrag]".
               { apply auth_update_alloc. apply gset_local_update. set_solver. }
               (* Closing the socket invariant. *)
               iSplitL "Hh Hmh HmTauth".
               { iModIntro. iNext. iExists R', ({[resp]} ∪ T').
                 iFrame; eauto. iSplit; first eauto. iSplitL; last done.
               iExists ({[resp]} ∪ T0). eauto with set_solver. }
               iModIntro. do 4 wp_pure _.
               (* It remains now to establish the post-condition,
                  i.e. that the loop-invariant of
                  the server listen holds. *)
               iApply "HΦ". iSplit; first done.
               iExists _, _, _, _, _, _.
               iSplit; [done|].
               (* The socket of the server is still in the listening mode. *)
               iSplitL "Hskl"; [done|].
               (* Establish that conn_map_resources hold. *)
               iSplitL.
               { iExists ({[m]} ∪ R), ({[resp]} ∪ T0), cmv'.
                 iExists (<[m_sender m:=γs]> γM), (<[m_sender m:=HalfOpened ckn]> cM).
                 iFrame "#∗"; eauto.
                 iSplit; first done.
                 iSplit; [ by rewrite !dom_insert_L Hdom |].
                 (* It is convenient to show that the case m ∈ R is absurd. *)
                 destruct (bool_decide (m ∈ R)) eqn:Hm.
                 { apply bool_decide_eq_true_1 in Hm.
                   iAssert (∃ cs, ⌜cM !! m_sender m = Some cs⌝)%I as "%Habs".
                   { iDestruct (big_sepS_elem_of _ R m Hm with "HmsgRres") as "Hres".
                     iDestruct "Hres"
                       as (γs0 mval0 n0 Hser0) "(#Htk0 & [#(%Hl & %Hl2) | #Hr])"; [eauto|].
                     iDestruct "Hr" as (???) "%Habs"; eauto. }
                   naive_solver. }
                 (* So, now we know that m ∉ R. *)
                 apply bool_decide_eq_false_1 in Hm.
                 iDestruct "HmRfrag" as (R0 HsubR0) "#HfragR0".
                 (* The first part: domain. *)
                 iSplit.
                 { iApply (big_sepS_insert with "[HdomR]"); first done. simpl.
                   iSplit.
                   - iPureIntro; rewrite dom_insert; set_solver.
                   - iApply (big_sepS_mono with "[$HdomR]").
                     iIntros. iPureIntro. set_solver. }
                 (* The second part: initial shape. *)
                 iSplit.
                 { iApply (big_sepS_insert with "[HmsgRres]"); first done.
                 iSplit.
                   - iExists γs, (InjLV (#s, #i)), ckn.
                     rewrite Hseq lookup_insert Hargeq.
                     rewrite Hargeq Hseq in Hser.
                     eauto.
                   - iApply (big_sepS_mono _ _ _ with "HmsgRres").
                     iIntros (m0 Hm0) "#Hres".
                     destruct (bool_decide (m_sender m = m_sender m0)) eqn:Hmeq.
                     + apply bool_decide_eq_true_1 in Hmeq.
                       iDestruct "Hres"
                          as (γs0 mval0 n0 Hser0) "(#Htk0 & [#(%Hl & %Hl2) | #Hr])".
                        * rewrite -Hmeq in Hl2. naive_solver.
                        * iDestruct "Hr" as (???) "%Habs".
                          rewrite -Hmeq in Habs. naive_solver.
                     + apply bool_decide_eq_false_1 in Hmeq.
                       iDestruct "Hres"
                          as (γs0 mval0 n0 Hser0) "(#Htk0 & [#(%Hl & %Hl2) | #Hr])".
                       * iExists γs0, _, _. iFrame "#∗". iSplit; first done.
                         iLeft. by rewrite lookup_insert_ne.
                       * iDestruct "Hr" as (???) "%Habs".
                         iExists γs0, _, n0. iFrame "#∗". iSplit; first done.
                         iRight. rewrite lookup_insert_ne; subst; eauto. }
                 (* The third part: spatial resources and input/output relation. *)
                 iApply (big_sepM_insert with "[-]").
                 { rewrite -Hdom in Hdomc. done. }
                 simpl.
                 (* First, show for the new message. *)
                 iSplitR "HknRes".
                 { iExists γs, ckn. iSplitL "Hstk HckF".
                   iSplitL "Hstk"; [done|].
                   iFrame "HckF".
                   iSplit.
                   - subst. iExists m, (InjLV (#"INIT", #0)).
                     iSplit; first eauto with set_solver.
                     (* TODO. add missing hypothesis *)
                     iPureIntro. rewrite Hseq Hargeq in Hser. split_and!; try eauto.
                   - iExists resp, (InjLV (#"INIT-ACK", #ckn)).
                       eauto with set_solver.
                   - simpl. iLeft. by iFrame. }
                 (* Now, show the monotonicity property. *)
                 iApply (big_sepM_mono _ _  with "[$HknRes]").
                 iIntros (a b Hab) "Hres".
                 iDestruct "Hres" as "(%y & %w & ((#Htk & Hf & %Hy11 & %Hy12) & Hdisj))".
                 iExists y, w. iSplitL "Htk Hf". iSplitR; first done. iFrame "#∗".
                   destruct Hy11 as (m1 & v1 & Hm1 & Hser1 & Hdest1 & Hsender1 & Hv1).
                   destruct Hy12 as (m2 & v2 & Hm2 & Hser2 & Hdest2 & Hsender2 & Hv2).
                   iSplit; iPureIntro; simpl.
                   - exists m1, v1. split_and!; eauto with set_solver.
                   - exists m2, v2. split_and!; [set_solver |done ..].
                   - iDestruct "Hdisj" as "[(%Hy1 & Hy2 & Hy3 )|Hy]".
                     (* First sub-case: connection is half-opened. *)
                     + destruct (bool_decide (m_sender m = a)) eqn:Hmeq.
                       * apply bool_decide_eq_true_1 in Hmeq as <-. naive_solver.
                       * apply bool_decide_eq_false_1 in Hmeq.
                         iLeft. iFrame. simpl in *. eauto.
                     (* Second sub-case: connection is established. *)
                     + iDestruct "Hy" as (γc c r1 r2 r3 r4 Heq1) "Hres".
                       iDestruct "Hres" as (Hresp HcmA) "(Hr2 & Hr3 & Hr4 & Hr5)".
                       iRight.
                       iExists _, _, _, _, _, _.
                       iFrame.
                       iSplit; iPureIntro; simpl.
                       ++ destruct Heq1 as (m1 & v1 & Hm1 & Hser1 & Hdest1 & Hsender1 & Hv1).
                          exists m1, v1. split_and!; eauto with set_solver.
                       ++ split.
                          destruct Hresp as (m2 & v2 & Hm2 & Hser2 & Hdest2 & Hsender2 & Hv2).
                          exists m2, v2. split_and!; [set_solver |done ..].
                          destruct (bool_decide (m_sender m = a)) eqn:Hmeq.
                          { apply bool_decide_eq_true_1 in Hmeq as <-.
                            assert (is_Some (γM !! m_sender m)) as Habs by naive_solver.
                            apply elem_of_dom in Habs. by rewrite Hdom in Habs. }
                          by apply bool_decide_eq_false_1 in Hmeq. }
               (* Finally, show that socket and connection queue invariants are preserved. *)
               iSplitL. iExists _, _. by iFrame "#∗"; eauto. eauto.
         (* Ignore the message otherwise. *)
         ---  wp_pure _. by iDestruct "HRes" as "[(-> & _ & -> & _)|(-> & _) ]".
      (* Show that other cases are absurd. *)
      -- do 2 wp_pure _.
         iDestruct "HRes" as "[(-> & _ & -> & _)|(-> & -> & Hck & (%γs & #Htk) & _)]"; first done.
         iDestruct (own_valid_2 with "HknM Htk") as %[Hsubl _]%auth_both_valid_discrete.
         apply gmap.dom_included in Hsubl.
         rewrite dom_singleton in Hsubl.
         apply singleton_subseteq_l in Hsubl.
         rewrite -Hdom in Hdomc.
         set_solver.
    (* Show that other cases are absurd. *)
    - iDestruct "HrRes" as "(_ & [(%ackid & -> & Hack) | (%i & %w & -> & Hmsg)])".
      wp_pures.
      + iDestruct "Hack" as (n -> γs) "(#Htk & _)".
        iDestruct (own_valid_2 with "HknM Htk") as %[Hsubl _]%auth_both_valid_discrete.
        apply gmap.dom_included in Hsubl.
        rewrite dom_singleton in Hsubl.
        apply singleton_subseteq_l in Hsubl.
        rewrite -Hdom in Hdomc.
        set_solver.
      + iDestruct "Hmsg" as (n _ γs) "(#Htk & _)".
        iDestruct (own_valid_2 with "HknM Htk") as %[Hsubl _]%auth_both_valid_discrete.
        apply gmap.dom_included in Hsubl.
        rewrite dom_singleton in Hsubl.
        apply singleton_subseteq_l in Hsubl.
        rewrite -Hdom in Hdomc.
        set_solver.
  Qed.

End Proof_of_server_conn_step_1.
