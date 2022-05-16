From iris.proofmode Require Import tactics.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants mono_nat.
From stdpp Require Import namespaces.
From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_code network_util_proof.
From aneris.aneris_lang.lib Require Import assert_proof.
From aneris.aneris_lang.lib Require Import lock_proof list_proof queue_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.resources Require Import
     chan_endpoints_resources socket_interp.
From aneris.examples.reliable_communication.proof Require Import
     proof_of_recv_on_chan.

Section Proof_of_client_recv_loop.
  Context `{!anerisG Mdl Σ,
            !Reliable_communication_service_params,
            !chanG Σ,
            !lockG Σ}.
  Context `{!server_ghost_names}.
  Context (N : namespace).

  Lemma client_recv_on_chan_loop_spec c ip skt sa
        (γs : session_name) (γe : endpoint_name)
        ser serf
        (sidLBLoc ackIdLoc : loc) (sbuf : loc) slk (rbuf : loc) rlk
        (ridx ackId : nat) :
    ip_of_address sa = ip →
    endpoint_chan_name γe = session_chan_name γs →
    lock_idx_name (endpoint_send_lock_name γe) = (session_clt_idx_name γs) →
    c = (((#sbuf, slk), (#rbuf, rlk)), serf)%V →
    {{{ socket_resource skt sa N Left ∗
        RCParams_srv_saddr ⤇ server_interp ∗
        is_recv_lock
          ip (endpoint_chan_name γe) (endpoint_recv_lock_name γe)
          rlk rbuf ackIdLoc Left ∗
        is_send_lock
          ip (endpoint_chan_name γe) (endpoint_send_lock_name γe)
          slk sbuf ser sidLBLoc Left ∗
        sidLBLoc ↦[ip]{1/2} #ridx ∗
        ackIdLoc ↦[ip]{1/2} #ackId ∗
        session_token sa γs ∗
        mono_nat_lb_own (session_srv_idx_name γs) ackId }}}
      client_recv_on_chan_loop skt #RCParams_srv_saddr #sidLBLoc #ackIdLoc c @[ip]
    {{{ w, RET w; False }}}.
  Proof.
    iIntros (<- Heqc Heqg -> Φ) "(#Hskt & #Hsrv & #Hrlk & #Hslk & HsidLB &
      Hack & #Htok & Hsidx) HΦ".
    iDestruct "Hskt" as (sh sock -> Haddr Hblock) "[#Hinterp #Hsk]".
    wp_lam. wp_pures.
    iLöb as "Hlob" forall (ridx ackId Φ).
    iDestruct "Hsidx" as "#Hsidx".
    wp_bind (ReceiveFrom _).
    iInv N as (R T) "(Hsh & HRT & IH)".
    wp_apply (aneris_wp_receivefrom with "[$Hsh $HRT $Hinterp]"); [done..|].
    iIntros (m) "[%Hdest H]".
    iAssert (∃ R T, sh ↪[ ip_of_address sa] sock ∗ sa ⤳ ({[m]} ∪ R, T) ∗
            [∗ set] m ∈ {[m]} ∪ R, client_server_interp_pers Left m)%I
      with "[H IH]" as (R' T') "(Hsh & Hsa & HR)".
    { iDestruct "H" as
        "[(%Hnin & Hsh & Hsa & _ & Hw) |
          (%Hin & Hsh & Hsa)]".
      { iExists _, _. iFrame.
        rewrite big_sepS_union; [|set_solver].
        rewrite big_sepS_singleton.
        iFrame. iDestruct "IH" as "(#Hdom & #(IH1 & IH2))".
        iSplitL; [iFrame; by iApply client_interp_le | done ]. }
      assert (R = {[m]} ∪ R ∖ {[m]}) as ->.
      { apply union_difference_L. set_solver. }
      iExists _, _. iDestruct "IH" as "(#Hdom & #IH1 & #IH2)". by iFrame. }
    iModIntro.
    iAssert (client_server_interp_pers Left m)%I with "[HR]"
      as (mval Heq Hser) "#Hmval".
    { rewrite big_sepS_elem_of_acc_impl.
      by iDestruct "HR" as "[$ _]". set_solver. }
    iSplitL "Hsh Hsa HR".
    { iModIntro. iExists _, _. by iFrame "Hsh Hsa HR". }
    wp_pures.
    wp_apply (wp_unSOME); [done|].
    iIntros "_".
    wp_pure _. wp_pure _.
    wp_apply wp_assert.
    wp_pures.
    iSplit.
    { iPureIntro. subst. rewrite Heq. by case_bool_decide. }
    iIntros "!>".
    wp_pures.
    wp_bind (sum_deser _ _ _).
    wp_apply (s_deser_spec (msg_serialization RCParams_srv_ser) _ mval); [done|].
    iIntros "_".
    iDestruct "Hmval" as "[Hmval | Hmval]".
    { iDestruct "Hmval" as (str i ->) "_". wp_pures.
      iApply ("Hlob" with "HsidLB Hack Hsidx HΦ"). }
    iDestruct "Hmval" as "(#Hsmode & [Hmval | Hmval])".
    { iDestruct "Hmval" as (ackid) "[-> [%n [-> [%γ [Htok' Hsidx']]]]]". wp_pures.
      wp_apply (process_data_on_chan_spec _ _ _ _ _ γs γe ser serf sidLBLoc ackIdLoc Left _
               with "[$Hsrv $Hrlk $Hslk $HsidLB $Hack]");
      [done|done|done|done|done| | ].
      { iSplit; [by iFrame "#"; iExists _, _; iFrame "#"|].
        iFrame "#".
        iSplitL.
        iLeft. iExists _. iSplit; [done|]. iExists _.
        iSplit; [done|]. iExists _. subst. iFrame "#".
      subst; eauto. }
      iDestruct 1 as (ridx' ackId') "(HsidLB & Hack & Hsidx''
        & %Hridx & %HackId)".
      wp_pures. subst.
      iDestruct (session_token_agree with "Htok' Htok") as %Heq'.
      simplify_eq. wp_pures.
      iApply ("Hlob" with "HsidLB Hack Hsidx'' HΦ"). }
    iDestruct "Hmval" as (i w ->) "Hmval". wp_pures.
    wp_apply (process_data_on_chan_spec
                _ _ _ _ _ γs γe ser serf sidLBLoc ackIdLoc Left _
               with "[$Hsrv $Hrlk $Hslk $HsidLB $Hack Hmval]");
      [done|done|done|done|done| |].
    { iSplit; [by iFrame "#"; iExists _, _; iFrame "#"|].
      iFrame "#". iSplitL.
      iRight.
      iDestruct "Hmval" as (n Hn) "Hmval".
      rewrite -(Z2Nat.id i); [|lia]. iExists _, _. iSplit; [done|].
      iDestruct "Hmval" as (γ') "[Htok' [Hfrag Hsidx'']]".
      subst.
      iDestruct (session_token_agree with "Htok Htok'") as %Heq'.
      simplify_eq.
      rewrite Nat2Z.id. rewrite Nat.add_1_r. simpl. rewrite Heqc. iFrame "#".
      subst; eauto. }
    iDestruct 1 as (ridx' ackId') "(HsidLB & Hack & Hsidx'' & %Hridx & %HackId)".
    wp_pures.
    by iApply ("Hlob" with "HsidLB Hack Hsidx'' HΦ").
  Qed.

End Proof_of_client_recv_loop.
