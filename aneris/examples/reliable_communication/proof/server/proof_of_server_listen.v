From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants mono_nat.
From iris.algebra.lib Require Import excl_auth.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_proof.
From aneris.aneris_lang.lib Require Import lock_proof map_proof queue_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.resources Require Import
     chan_endpoints_resources
     socket_interp.
From aneris.examples.reliable_communication.proof.common_protocol Require Import
     proof_of_send_from_chan_loop.
From aneris.examples.reliable_communication.proof.server Require Import
     server_resources
     proof_of_server_conn_step_to_open_new_conn
     proof_of_server_conn_step_to_establish_conn
     proof_of_server_conn_step_process_data.

Section Proof_of_server_listen.
  Context `{!anerisG Mdl Σ, !Reliable_communication_service_params, !chanG Σ, !lockG Σ}.
  Context `{!server_ghost_names}.
  Context (N : namespace).
  Notation srv_ip := (ip_of_address RCParams_srv_saddr).

  Lemma server_recv_on_listening_skt_loop_spec (skt_passive : val) :
    {{{ isServer_listening_loop_resources skt_passive }}}
      server_recv_on_listening_skt_loop skt_passive @[srv_ip]
    {{{ w, RET w; False }}}.
  Proof.
    iIntros (Φ) "HsrRes HΦ".
    iDestruct "HsrRes"
      as (skl skt cml cql qlk γqlk Hsktsrv) "(Hsl & HcmRes & HsRes & #Hqlk)".
    rewrite Hsktsrv.
    iDestruct "HsRes" as (h sock) "(%Hskt & %Hsaddr & %Hsblk & #Hsi & #Hsinv)".
    wp_lam.
    wp_pures.
    rewrite Hskt.
    do 17 wp_pure _.
    wp_pure _.
    wp_let.
    iLöb as "IH" forall (skl cml Hsktsrv).
    wp_pures.
    wp_bind (ReceiveFrom _).
    (* Open the socket invariant and extract tracked message resources. *)
    iInv (RCParams_srv_N.@"skt") as (R T)  "(>Hh & >Hmh & >HtrackedR & >HtrackedT & #HmR)".
    iDestruct "HtrackedR" as (R1 Hsub1) "#HfragR1".
    iDestruct "HtrackedT" as (T1 Hsub2) "HauthT1".
    (* Receive a new message. *)
    wp_apply (aneris_wp_receivefrom with "[$Hh $Hmh]"); [done..|].
    iIntros (m) "[%Hdest Hm]".
    (* Factor out socket resources out of the disjunction. *)
    (* This should be a separate aneris lemma. *)
    iAssert (h ↪[srv_ip] sock ∗
               RCParams_srv_saddr ⤳ ({[m]} ∪ R, T) ∗
               ([∗ set] m' ∈ ({[m]} ∪ R), client_server_interp_pers Right m') ∗
               ((⌜m ∉ R⌝ ∗ server_interp m) ∨ (⌜m ∈ R⌝)))%I
      with "[Hm]" as "(Hh & Hmh & #HmR' & HR)".
    { iDestruct "Hm" as "[(%Hmnotin & Hh & Hmh & _ & Hmres)|(%Hmin & Hh & Hmh)]".
      - iFrame.
        iAssert (client_server_interp_pers Right m) with "[Hmres]"
          as "#HmResPers".
        { iApply (server_interp_le with "[$Hmres]"). }
        iSplitR. { by iApply (big_sepS_insert with "[$HmR]"). }
        iLeft. by iFrame.
      - iFrame.
        replace ({[m]} ∪ R) with R by set_solver.
        iFrame "#∗".
        by iRight. }
    (* Destruct connection map resources. *)
    iDestruct "HcmRes"
      as (R0 T0 cmv γM cM Hmap Hdom)
           "(HmrFull & #HmtFrag & #Hdomfrag & #HmsgRres & Hcml & HknM & HknRes)".
    (* Obtain the fragment for the server message history ghost state.  *)
    iMod (own_update _ _ (● R0 ⋅ ◯ R0) with "HmrFull") as "[HmrFull #Hfrag]".
    { apply auth_update_alloc. by apply gset_local_update. }
    iAssert (⌜R ⊆ R0⌝)%I as "%HmhrRel".
    {  iDestruct (own_valid_2 with "HmrFull HfragR1")
        as %[Hv1%gset_included Hv2]%auth_both_valid_discrete.
       iPureIntro. set_solver. }
    (* Update the server message history resource. *)
    iMod (own_update_2 _ _ _ (● ({[m]} ∪ R0) ⋅ ◯ ({[m]} ∪ R0))
           with "HmrFull Hfrag") as "[Hr1 #Hr2]".
    { apply auth_update. apply gset_local_update. set_solver. }
    iModIntro.
    (* Close the socket invariant. *)
    iSplitL "Hh Hmh HauthT1".
    { iModIntro.
      iExists _, _.
      iFrame; eauto. simpl.
      iFrame "#".
      iSplit.
      - iExists ({[m]} ∪ R0).
        iSplit; last by iFrame; eauto.
        iPureIntro; set_solver.
      - iExists _. eauto with set_solver. }
    (* Obtain the persistent part of the client resources. *)
    (* Could be a separate lemma in the socket_interp resources. *)
    iAssert (client_server_interp_pers Right m)%I as "#HmsgResPers".
    { destruct (bool_decide (m ∈ R)) eqn:Hm.
      - apply bool_decide_eq_true_1 in Hm.
        replace ({[m]} ∪ R) with R by set_solver.
        by iApply (big_sepS_elem_of with "[$HmR]").
      - apply bool_decide_eq_false_1 in Hm.
        by iPoseProof
           (big_sepS_insert
              (λ m', client_server_interp_pers Right m') R m with "HmR'")
          as "(Ha & Hb)"; first done. }
    iDestruct "HmsgResPers" as (mval) "(#Hclt_si & (%Hser & #HmvalRes))".
    (* Retrieve and deserialize the message. *)
    wp_pures.
    wp_apply (wp_unSOME); [done|].
    iIntros "_".
    wp_pures.
    wp_bind (sum_deser _ _ _). simpl.
    wp_apply (s_deser_spec (msg_serialization RCParams_clt_ser) _ _); [done|].
    iIntros "_".
    wp_pures. rewrite -Hskt.
    (* Check whether the sender of the message is known. *)
    wp_load.
    wp_apply (wp_map_lookup srv_ip _ cmv cM); [done |].
    iIntros (v Hv).
    destruct (bool_decide (is_Some (cM !! m_sender m))) eqn:Hsm.
    (* Case 1. Client is known *)
    { apply bool_decide_eq_true_1 in Hsm.
      specialize (elem_of_dom cM (m_sender m)) as (_ & Hdomc).
      specialize (Hdomc Hsm).
      destruct Hsm as [cs Hcs].
      rewrite Hcs in Hv.
      iAssert  ((⌜m ∉ R⌝ ∗ server_interp m ∨ ⌜m ∈ R⌝ -∗ ⌜m ∈ R0⌝ ∨ server_interp m)%I)
        as "Hrd".
      { iIntros "[(Hl & $) |%Hr]".
        iLeft. iPureIntro. set_solver. }
      iDestruct ("Hrd" with "HR") as "HR".
      destruct cs as [cookie|((cdata, ck) & (ackId, sidLBid))]; rewrite Hv.
      (* Case 1.1 Known client, half-opened connection.  *)
      -- wp_pures.
         wp_apply (server_conn_step_to_establish_conn_spec
                     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R0
                    with "[-HΦ] [HΦ]");
        [done .. | | ].
      - iFrame "HR". iFrame "#∗"; eauto.
      - iNext. iIntros (v0) "(-> & Hres)".
        do 2 wp_pure _.
        iDestruct "Hres" as (skl' skt' cml' cql' qlk' γqlk' Hsktsrv')
                              "(Hsl & HcmRes & HsRes & #Hqlk')".
        rewrite Hsktsrv' in Hsktsrv. inversion Hsktsrv. subst.
        iApply ("IH" with "[] [$Hsl] [-HΦ] [HΦ]"); [naive_solver | iFrame |done].
      (* Case 1.2. Known client, established connection.  *)
      -- wp_pures.
         wp_apply (server_conn_step_process_data_spec with "[-HΦ] [HΦ]");
        [done .. | | ].
      - iFrame "HR". iSplit; first done. iFrame "#∗"; eauto.
      - iNext. iIntros (v0) "(-> & Hres)".
        do 2 wp_pure _.
        iDestruct "Hres" as (skl' skt' cml' cql' qlk' γqlk' Hsktsrv')
                              "(Hsl & HcmRes & HsRes & #Hqlk')".
        rewrite Hsktsrv' in Hsktsrv. inversion Hsktsrv. subst.
        iApply ("IH" with "[] [$Hsl] [-HΦ] [HΦ]"); [naive_solver | iFrame |done]. }
    (* Case 1.3. The client is not known. Open a new half-opened connection. *)
    apply bool_decide_eq_false_1, eq_None_not_Some in Hsm.
    specialize (not_elem_of_dom cM (m_sender m)) as (_ & Hdomc).
    specialize (Hdomc Hsm).
    rewrite Hsm in Hv. rewrite Hv.
    wp_pures.
    iDestruct "HR" as "[(%Hmnotin & Hmres)|%Hmin]".
    (* Message is fresh *)
    { iDestruct "Hmres" as (mval' Hser') "(#Hcsi & HmvalRes')".
      assert (mval' = mval) as Heqval.
      { by eapply (msg_ser_is_ser_injective Left (m_body m) _ _). }
      rewrite Heqval.
      wp_apply (server_conn_step_to_open_new_conn_spec with "[-HΦ] [HΦ]");
        [done .. | | ].
      - iSplit; first done. iFrame "#∗"; eauto.
      - iNext. iIntros (v0) "(-> & Hres)".
        do 2 wp_pure _.
        iDestruct "Hres" as (skl' skt' cml' cql' qlk' γqlk' Hsktsrv')
                              "(Hsl & HcmRes & HsRes & #Hqlk')".
        rewrite Hsktsrv' in Hsktsrv. inversion Hsktsrv. subst.
        iApply ("IH" with "[] [$Hsl] [-HΦ] [HΦ]"); [naive_solver | iFrame |done]. }
    (* Message is a duplicate. *)
    iDestruct (big_sepS_elem_of _ _ m with "Hdomfrag") as "%Habs"; [set_solver|].
    by rewrite Hdom in Habs.
  Qed.

  Lemma server_listen_internal_spec (skt : val) :
    {{{ isServerSocketInternal skt false }}}
      server_listen skt @[ip_of_address RCParams_srv_saddr]
    {{{ RET #(); isServerSocketInternal skt true }}}.
  Proof.
    iIntros (Φ) "HsrvRes HΦ".
    iDestruct "HsrvRes" as (srv_skt_l <-) "[(_ & HsrvRes)|(%Habs & _)]"; [|done].
    iDestruct "HsrvRes"
      as (skt h s) "(Hl & Hskt & Hmh & Hkn & HknR1 & #HknR2 & HknT1 & #HknT2)".
    wp_lam. wp_load. wp_pures.
    wp_apply (@wp_map_empty _ _ _ _ _ _ Inject_socket_address _ Inject_conn_state); [done|].
    iIntros (cv Hcv).
    wp_alloc cmLoc as "Hml".
    wp_pures.
    wp_apply (@wp_queue_empty _ _ _ val _); [done|].
    iIntros (qv Hqv).
    wp_alloc qLoc as "Hql".
    wp_pures.
    wp_apply
      (newlock_spec (RCParams_srv_N .@ "qlk") srv_ip (conn_queue_lock_def qLoc)
        with "[Hql] [Hml Hl Hskt Hmh Hkn HΦ HknR1 HknT1]").
    - iExists qv, []. iFrame "#∗"; eauto.
    - iNext. iIntros (qlk γ_qlk) "#Hqlk".
      wp_pures. wp_store. wp_pures.
      iDestruct "Hskt" as "(HisSkt & %Hsa & %Hsblk & Hh & #Hsi)".
      iMod ((inv_alloc
               (RCParams_srv_N .@"skt")
               _ (socket_inv_def h RCParams_srv_saddr s Right))
             with "[Hh Hmh HknT1]") as "#Hsock_inv".
      { iNext. iExists _, _. iFrame "#∗". simpl. iSplit; eauto. }
      iDestruct (fractional.fractional_split_1
                   _ _ _ _  (1/3)%Qp (2/3)%Qp with "[Hl]") as "(Hl1 & Hl2)";
        [apply mapsto_heap_as_fractional .. | |].
      { replace (1 / 3 + 2 / 3)%Qp with 1%Qp; first by iFrame.
        rewrite -Qp_div_add_distr pos_to_Qp_add Qp_div_diag //=. }
      wp_apply (aneris_wp_fork with "[-]").
      iSplitL "HΦ Hl2".
      + wp_pures. iApply "HΦ". iNext. iExists srv_skt_l. iSplit; [done|].
        iRight.
        iSplit; [done|].
        iExists _, _, _.
        iFrame "#∗".
      + iNext.
        iApply (server_recv_on_listening_skt_loop_spec with "[-]"); last done.
        iExists srv_skt_l, skt, cmLoc, qLoc, qlk, γ_qlk.
        iSplit; [done|].
        iFrame "#∗".
        iSplitL "Hml Hkn HknR1".
        ++ iExists ∅, ∅, cv, ∅, ∅. iSplit; [done|].
           iSplit; [iPureIntro; set_solver|].
           iFrame "#∗". eauto.
        ++ iExists _, _;  iFrame "#∗"; eauto.
  Qed.

End Proof_of_server_listen.
