From iris.proofmode Require Import tactics.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants mono_nat.
From stdpp Require Import namespaces.
From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.aneris_lang.lib Require Import assert_proof lock_proof monitor_proof queue_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.reliable_communication Require Import client_server_code user_params.
From aneris.examples.reliable_communication.resources Require Import
     chan_endpoints_resources socket_interp.

Section Proof_of_make_phys_resources.
  Context `{!anerisG Mdl Σ}.
  Context `{!chanG Σ}.
  Context `{!lockG Σ}.
  Context `{!server_ghost_names}.
  Context `{!Reliable_communication_service_params}.

  (* TODO: move to queue lib *)
  Lemma is_queue_empty v : is_queue [] v <-> v = (InjLV #(), InjLV #())%V.
    Proof.
      split.
      - destruct 1 as (vl & vr & lf & lb & Heq1 & Hl1 & Hl2 & Hempty).
        simplify_eq. symmetry in Hempty.
        apply app_eq_nil in Hempty as (He1 & He2).
        rewrite -reverse_nil in He2.
        by simplify_eq /=.
      - move ->. do 2 eexists. exists [], []. split_and!; naive_solver.
    Qed.

    Lemma make_new_channel_descr_spec
          (γs : session_name) sa (p : iProto Σ) s ackIdLoc sidLBLoc (serf : val) lsa :
      lsa = side_elim s sa RCParams_srv_saddr →
      p = side_elim s RCParams_protocol (iProto_dual RCParams_protocol) →
      serf = side_elim s
               (s_ser (s_serializer RCParams_clt_ser))
               (s_ser (s_serializer RCParams_srv_ser)) →
    {{{
        can_init γs sa p s ∗
        ackIdLoc ↦[ip_of_address lsa]{1/2} #0 ∗
        sidLBLoc ↦[ip_of_address lsa]{1/2} #0}}}
       make_new_channel_descr serf
       @[ip_of_address lsa]
     {{{ γe c, RET c;
         ChannelAddrToken
           γe (side_elim s (sa, RCParams_srv_saddr) (RCParams_srv_saddr, sa)) ∗
         ChannelSideToken γe s ∗
         ChannelIdxsToken γe (sidLBLoc, ackIdLoc) ∗
         c ↣{ γe, ip_of_address lsa, (side_elim s RCParams_clt_ser RCParams_srv_ser)} p
     }}}.
  Proof.
    set (ip := ip_of_address lsa).
    set (γc := session_chan_name γs).
    set (ser := side_elim s RCParams_clt_ser RCParams_srv_ser).
    set (src_sa := side_elim s sa RCParams_srv_saddr).
    set (dst_sa := side_elim s RCParams_srv_saddr sa).
    set (γsidx := side_elim s (session_clt_idx_name γs) (session_srv_idx_name γs)).
    iIntros (Hp Hserf -> Φ) "(Hinit & HackIdLoc & HsidLBLoc) HΦ".
    wp_lam.
    wp_apply wp_queue_empty; first done.
    iIntros (v) "%Hq".
    wp_alloc sbuf as "Hsb".
    wp_pures.
    wp_apply wp_queue_empty; first done.
    iIntros (v') "%Hq'".
    wp_alloc rbuf as "Hrb".
    wp_pures.
    iDestruct "Hinit" as "(#Hst & (HmonoF1 & HmonoF2) & #Hmono & Hchan_res)".
    wp_apply (new_monitor_spec (chan_N γc .@ "slk") ip
                (send_lock_def ip γc γsidx sbuf sidLBLoc ser s)
               with "[Hsb HsidLBLoc HmonoF1]").
    { iExists _, [], 0. rewrite -(Nat2Z.inj_add 0 0).
      simplify_eq /=. by iFrame "#∗". }
    iIntros (γ_slk slk) "Hslk". wp_pures.
    wp_apply fupd_aneris_wp.
    iMod (mono_nat_own_alloc 0%nat) as (γridx) "((HridxA1 & HrdixA2) & HridxF)".
    iMod (own_alloc (@to_agree _ (src_sa, dst_sa))) as (γ_addr) "#Haddr"; first done.
    iMod (own_alloc (to_agree s)) as (γ_side) "#Hside"; first done.
    iMod (own_alloc (to_agree (sidLBLoc, ackIdLoc))) as (γ_idxs) "#Hidxs"; first done.
    iModIntro.
    wp_apply (newlock_spec
                (chan_N γc .@ "rlk") ip
                (recv_lock_def ip γc γridx rbuf ackIdLoc s)
               with "[Hrb HackIdLoc HridxA1]").
    { iExists _, [], 0. rewrite -(Nat2Z.inj_add 0 0).
      simplify_eq /=. by iFrame "#∗". }
    iIntros (rlk γ_rlk) "Hrlk". wp_let.
    set (γslk := LockName γ_slk γsidx).
    set (γrlk := LockName γ_rlk γridx).
    set (γe := EndpointName γc γslk γrlk γ_addr γ_side γ_idxs).
    wp_alloc serl as "Hserl".
    wp_pures.
    iApply ("HΦ" $! γe with "[-]"). simpl in *. iFrame "#".
    iSplit; first by destruct s; eauto.
    rewrite{1} /iProto_mapsto seal_eq /iProto_mapsto_def.
    iExists γs, s, serl, _.
    iExists src_sa, dst_sa.
    iExists sbuf, slk, rbuf.
    iExists rlk, sidLBLoc, ackIdLoc, 0, 0.
    do 3 (iSplit; first done).
    iFrame "#∗".
    iSplit; first by destruct s; iFrame "#∗".
    destruct s; eauto.
  Qed.

End Proof_of_make_phys_resources.
