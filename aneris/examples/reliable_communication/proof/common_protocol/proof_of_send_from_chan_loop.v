From iris.proofmode Require Import tactics.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants mono_nat.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.aneris_lang.lib Require Import lock_proof monitor_proof queue_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.resources Require Import
     chan_endpoints_resources
     socket_interp.

Section Proof_of_send_loop.
  Context `{!anerisG Mdl Σ,
            !Reliable_communication_service_params,
            !chanG Σ,
            !lockG Σ}.
  Context `{!server_ghost_names}.
  Context (N : namespace).

  Lemma while_empty_loop_spec ip sa
        (γs : session_name) (γe : endpoint_name) γc
        sidLBLoc s (sbuf : loc) (serf : val) slk :
    ip_of_address sa = ip →
    γc = endpoint_chan_name γe →
    {{{ is_send_lock (ip_of_address sa) (endpoint_chan_name γe) (endpoint_send_lock_name γe) slk sbuf
             (side_elim s RCParams_clt_ser RCParams_srv_ser) sidLBLoc s ∗
        lock_proof.locked (lock_lock_name (endpoint_send_lock_name γe)) ∗
        send_lock_def (ip_of_address sa) (endpoint_chan_name γe) (lock_idx_name (endpoint_send_lock_name γe)) sbuf
            sidLBLoc (side_elim s RCParams_clt_ser RCParams_srv_ser) s }}}
       (rec: "while_empty_loop" "p" :=
        if: queue_is_empty (Fst ! "p") then monitor_wait slk;; "while_empty_loop" "p" else #())%V #sbuf @[ip]
    {{{ (q : val) (vs : list val) (sidLB : nat), RET #();
        lock_proof.locked (lock_lock_name (endpoint_send_lock_name γe)) ∗
        (sbuf ↦[ip] (q, #(sidLB + length vs)) ∗ ⌜is_queue vs q⌝ ∗
         sidLBLoc ↦[ip]{1 / 2} #sidLB ∗
         mono_nat_auth_own (lock_idx_name (endpoint_send_lock_name γe)) (1 / 2) (sidLB + length vs) ∗
         ([∗ list] i↦v ∈ vs, ∃ w : val, ⌜v = (#(sidLB + i), w)%V⌝ ∗
                               ⌜Serializable (side_elim s RCParams_clt_ser RCParams_srv_ser) w⌝ ∗
                               frag_list
                                 (side_elim s (chan_Tl_name (endpoint_chan_name γe))
                                    (chan_Tr_name (endpoint_chan_name γe))) (sidLB + i) w) ∗
        ⌜vs ≠ []⌝)%I
     }}}.
  Proof.
    iIntros (<- Heqc Φ) "(#Hslk & Hlocked & Hsdef) HΦ".
    iLöb as "Ilob".
    wp_pures.
    iDestruct "Hsdef" as (q vs sidLB') "(Hsbuf & %Hq & HsidLBLoc' & Hsidx & #Hvs)".
    wp_load.
    wp_pures. wp_apply (wp_queue_is_empty $! Hq).
    iIntros (b Hb).
    destruct b; wp_pures.
    { wp_pures.
      wp_smart_apply (monitor_wait_spec with "[$Hlocked $Hslk Hvs Hsbuf HsidLBLoc' Hsidx]").
      iExists _, _, _. by iFrame "#∗".
      iIntros (?) "(-> & Hlocked & Hsdef)".
      do 2 wp_pure _.
      iApply ("Ilob" with "[$Hlocked][Hsdef]"); [iFrame|done]. }
    iApply "HΦ".
    by iFrame "#∗".
  Qed.

  Lemma send_from_chan_loop_spec c ip skt sa dst
        (γs : session_name) (γe : endpoint_name)
        sidLBLoc s (sbuf : loc) (serf : val) slk rbuf rlk :
    ip_of_address sa = ip →
    endpoint_chan_name γe = session_chan_name γs →
    lock_idx_name (endpoint_send_lock_name γe) =
      side_elim s (session_clt_idx_name γs) (session_srv_idx_name γs) →
    c = (((#sbuf, slk), (#rbuf, rlk)), serf)%V →
    side_elim s dst sa = RCParams_srv_saddr →
    {{{ socket_resource skt sa N s ∗
        dst ⤇ side_elim s server_interp client_interp ∗
        is_send_lock
          ip (endpoint_chan_name γe)
          (endpoint_send_lock_name γe)
          slk sbuf
          (side_elim s RCParams_clt_ser RCParams_srv_ser) sidLBLoc s ∗
        session_token (side_elim s sa dst) γs ∗
        (∃ γs0 : session_name, session_connected (side_elim s sa dst) γs0)}}}
      send_from_chan_loop skt #dst c @[ip]
    {{{ w, RET w; False }}}.
  Proof.
    iIntros (<- Heqc Heqg -> Hsrv Φ) "(Hskt & #Hdst & #Hslk & #Htok & #Hsmode) HΦ".
    iDestruct "Hskt" as (sh sock -> Haddr Hblock) "[#Hinterp #Hsk]".
    wp_lam.
    do 39 wp_pure _.
    wp_lam.
    iLöb as "Ilob".
    wp_pures.
    wp_apply (monitor_acquire_spec with "Hslk").
    iIntros (v) "(-> & Hlocked & Hlk)".
    do 2 wp_pure _.
    set (γc := endpoint_chan_name γe).
    wp_apply (while_empty_loop_spec _ sa γs γe γc sidLBLoc s with "[$Hlocked $Hlk $Hslk][]");[done|done|done|].
    iNext. iIntros  (q vs sidLB') "(Hlocked & Hsbuf & %Hq & HsidLBLoc' & Hsidx & #Hvs & %Hneq)".
    wp_pures.
    iDestruct (mono_nat_lb_own_get with "Hsidx") as "#Hsidx'".
    wp_pures. wp_load. wp_pures.
    iDestruct (big_sepL_impl _
                (λ i v,
                   ⌜i < length vs⌝ ∗
                   ∃ w : val, ⌜v = (#(sidLB' + i), w)%V⌝ ∗
                               ⌜Serializable
                                  (side_elim s RCParams_clt_ser RCParams_srv_ser)
                                  w⌝ ∗
                               frag_list
                                 (side_elim s (chan_Tl_name γc) (chan_Tr_name γc))
                                 (sidLB' + i) w)%I with "Hvs []") as "#Hvs'".
    { iIntros "!>" (i v Hlookup) "H".
      iSplit; [|done].
      iPureIntro.
      apply lookup_lt_Some in Hlookup.
      lia. }
      wp_apply (wp_queue_iter_idx _ (λ _ _, True)%I True%I _ vs with "[] [$Hvs']");
        [|done|].
    { iIntros (i v). iIntros (Φ') "!> [_ [%Hle Hv]] HΦ'".
      iDestruct "Hv" as (w) "(-> & %Hser & Hfrag)".
      wp_pures.
      destruct s.
      - wp_apply (s_ser_spec (msg_serialization RCParams_clt_ser)).
        { iPureIntro. eexists _. right. split; [done|].
          eexists _. right. split; [done|]. eexists _, _. split; [done|].
          split; [|done]. eexists _. done. }
        iIntros (s His_ser).
        wp_pures.
        wp_bind (SendTo _ _ _).
        iInv N as "IH".
        iDestruct "IH" as (R T) "(Hsh & Hsa & IH)".
        wp_apply (aneris_wp_send with "[$Hsa $Hsh Hfrag]"); [done|done| |].
        { iFrame "Hdst".
          iIntros "!>". simpl.
          iExists (InjRV (InjRV _)).
          iSplit; [done|]. iSplit; [done|].
          iRight. iSplit; first done.
          iRight. iExists _, _. iSplit; [done|].
          iExists (sidLB' + i)%nat. iSplit; [iPureIntro; lia|].
          iExists _. iFrame "Htok". simpl. rewrite -Heqc. iFrame "Hfrag".
          rewrite Heqg.
          iApply (mono_nat_lb_own_le with "Hsidx'").
          lia. }
        iIntros "[Hsh Hsa] !>".
        iSplitL "Hsh Hsa IH".
        { iIntros "!>".
           iExists R, ({[{|
                m_sender := sa;
                m_destination := dst;
                m_body := s
              |}]} ∪ T). iFrame. }
        wp_pures; by iApply "HΦ'".
      - wp_apply (s_ser_spec (msg_serialization RCParams_srv_ser)).
        { iPureIntro. eexists _. right. split; [done|].
          eexists _. right. split; [done|]. eexists _, _. split; [done|].
          split; [|done]. eexists _. done. }
        iIntros (s His_ser).
        wp_pures.
        wp_bind (SendTo _ _ _).
        iInv N as "IH".
        iDestruct "IH" as (R T) "(Hsh & Hsa & IH)".
        wp_apply (aneris_wp_send with "[$Hsa $Hsh Hfrag]"); [done|done| |].
        { iFrame "Hdst".
          iIntros "!>". simpl.
          iExists (InjRV (InjRV _)).
          iSplit; [done|]. iSplit; [done|].
          iRight. iSplit; first done.
          iRight. iExists _, _. iSplit; [done|].
          iExists (sidLB' + i)%nat. iSplit; [iPureIntro; lia|].
          iExists _. iFrame "Htok". rewrite -Heqc Heqg. iFrame "Hfrag".
          simpl. iApply (mono_nat_lb_own_le with "Hsidx'").
          lia. }
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
        wp_pures; by iApply "HΦ'". }
    iIntros "_".
    wp_pures.
    wp_apply (monitor_release_spec with "[$Hlocked $Hslk Hsbuf HsidLBLoc' Hsidx]").
    iExists _, _, _. iFrame "#∗"; eauto.
    iIntros (v ->).
    do 4 wp_pure _.
    iApply "Ilob". by iIntros.
  Qed.

End Proof_of_send_loop.
