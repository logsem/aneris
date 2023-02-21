From iris.algebra Require Import agree gmap auth excl numbers frac_auth.
From iris.algebra.lib Require Import excl_auth mono_nat.
From iris.base_logic.lib Require Import invariants mono_nat.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang Require Import resources.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import lock_proof monitor_proof queue_proof map_proof.
From aneris.examples.reliable_communication.resources Require Export chan_session_resources.

Set Default Proof Using "Type".

(** Note that this file does not import user params, i.e.
    the definitions below are independent w.r.t. concrete physical/logical user parameters.  *)

(** Meta token tracking for each physical channel the corresponding endpoint ghost name. *)
(* TODO: define auth part, update, and alloc lemmas from all resources below. *)
Section Endpoint_MetaData.
  Context `{!anerisG Mdl Σ, !chanG Σ}.

  (** Meta token tracking for each physical channel the socket_address of the destination endpoint. *)
  Definition ChannelAddrToken
    (γe : endpoint_name) (sas : socket_address * socket_address) : iProp Σ :=
    own (endpoint_address_name γe) (to_agree sas).

  Lemma ChannelAddrToken_agree γe sa1 sa2 :
    ChannelAddrToken γe sa1 -∗ ChannelAddrToken γe sa2 -∗ ⌜sa1 = sa2⌝.
  Proof.
    iIntros "HA HB". iDestruct (own_valid_2 with "HA HB") as %Hval.
    iPureIntro. by apply (to_agree_op_inv_L (A:= _ )) in Hval.
  Qed.

  Definition ChannelSideToken (γe : endpoint_name) (s : side) : iProp Σ :=
    own (endpoint_side_name γe) (to_agree s).

  Lemma ChannelSideToken_agree γe s1 s2 :
    ChannelSideToken γe s1 -∗ ChannelSideToken γe s2 -∗ ⌜s1 = s2⌝.
  Proof.
    iIntros "HA HB". iDestruct (own_valid_2 with "HA HB") as %Hval.
    iPureIntro. by apply (to_agree_op_inv_L (A:=leibnizO _ )) in Hval.
  Qed.

  Definition ChannelIdxsToken (γe : endpoint_name) (pl : loc * loc) : iProp Σ :=
    own (endpoint_idxs_name γe) (to_agree pl).

  Lemma ChannelIdxsToken_agree γe pl1 pl2 :
    ChannelIdxsToken γe pl1 -∗ ChannelIdxsToken γe pl2 -∗ ⌜pl1 = pl2⌝.
  Proof.
    iIntros "HA HB". iDestruct (own_valid_2 with "HA HB") as %Hval.
    iPureIntro. destruct pl1. destruct pl2. simpl.
    by apply (to_agree_op_inv_L (A:= _ )) in Hval.
  Qed.

End Endpoint_MetaData.

Section iProto_endpoints.
  Context `{!anerisG Mdl Σ, !chanG Σ, !lockG Σ, !server_ghost_names}.

  Definition send_lock_def ip γc γidx sbuf sidLBLoc ser s : iProp Σ :=
    ∃ (q : val) (vs : list val) (sidLB : nat),
      sbuf ↦[ip] q ∗ ⌜is_queue vs q⌝ ∗
      sidLBLoc ↦[ip]{1/2} #sidLB ∗
      mono_nat_auth_own γidx (1/2) (sidLB + length vs) ∗
      [∗ list] i↦v ∈ vs,  ⌜Serializable ser v⌝ ∗
                          ses_idx (chan_session_escrow_name γc) s (sidLB+i) v.

  Definition is_send_lock ip γc γ_slk slk sbuf ser sidLBLoc s :=
    is_monitor ((chan_N γc) .@ "slk") ip (lock_lock_name γ_slk) slk
        (send_lock_def ip γc (lock_idx_name γ_slk) sbuf sidLBLoc ser s).

  Definition recv_lock_def ip γc γidx rbuf ackIdLoc s : iProp Σ :=
    ∃ (q : val) (vs : list val) (ridx : nat),
      rbuf ↦[ip] q ∗ ⌜is_queue vs q⌝ ∗
      ackIdLoc ↦[ip]{1/2} #(ridx + length vs) ∗
      mono_nat_auth_own γidx (1/2) ridx ∗
      [∗ list] i↦v ∈ vs, ses_idx (chan_session_escrow_name γc) (dual_side s)
                                 (ridx+i) v.

  Definition is_recv_lock ip γc γ_rlk rlk rbuf ackIdLoc s :=
    is_lock ((chan_N γc) .@ "rlk") ip (lock_lock_name γ_rlk) rlk
              (recv_lock_def ip γc (lock_idx_name γ_rlk) rbuf ackIdLoc s).

  Definition iProto_mapsto_def
            (γe : endpoint_name) (c : val)
            (ip : ip_address) (ser : serialization) (p : iProto Σ): iProp Σ :=
    ∃ (γs : session_name)
      (s : side)
      (serl : loc)
      (serf : val)
      (sa dst : socket_address)
      (sbuf : loc) (smn : val)
      (rbuf : loc) (rlk : val)
      (sidLBLoc ackIdLoc : loc)
      (sidx ridx : nat),
      ⌜c = (((#sbuf, smn), (#rbuf, rlk)), #serl)%V⌝ ∗
      ⌜endpoint_chan_name γe = session_chan_name γs⌝ ∗
      ⌜lock_idx_name (endpoint_send_lock_name γe) =
      side_elim s (session_clt_idx_name γs) (session_srv_idx_name γs)⌝ ∗
      serl ↦[ip] serf ∗
      ⌜s_ser (s_serializer ser) = serf⌝ ∗
      mono_nat_auth_own
        (lock_idx_name (endpoint_send_lock_name γe)) (1/2) sidx ∗
      mono_nat_auth_own
        (lock_idx_name (endpoint_recv_lock_name γe)) (1/2) ridx ∗
      session_token (side_elim s sa dst) γs ∗
      ChannelAddrToken γe (sa, dst) ∗
      ChannelSideToken γe s ∗
      ChannelIdxsToken γe (sidLBLoc, ackIdLoc) ∗
      ses_own
           (chan_N (endpoint_chan_name γe))
           (chan_session_escrow_name (endpoint_chan_name γe)) s sidx ridx p ∗
      is_send_lock ip
         (endpoint_chan_name γe)
         (endpoint_send_lock_name γe)
         smn sbuf ser sidLBLoc s ∗
      is_recv_lock ip
         (endpoint_chan_name γe)
         (endpoint_recv_lock_name γe)
         rlk rbuf ackIdLoc s.

  Definition iProto_mapsto_aux : seal (@iProto_mapsto_def).
    by eexists. Qed.
  Definition iProto_mapsto := unseal iProto_mapsto_aux.
  Definition iProto_mapsto_eq :
    @iProto_mapsto = @iProto_mapsto_def :=
    seal_eq iProto_mapsto_aux.
  Arguments iProto_mapsto _ _ _ _%proto.
  Global Instance: Params (@iProto_mapsto) 3 := {}.
  Notation "c ↣{ γe , ip , ser } p" := (iProto_mapsto γe c ip ser p)
                              (at level 20, format "c  ↣{ γe , ip , ser }  p").

  Global Instance iProto_mapsto_contractive γe c ip ser :
    Contractive (λ p, iProto_mapsto γe c ip ser p).
  Proof. rewrite iProto_mapsto_eq. solve_contractive. Qed.

  Global Instance iProto_mapsto_ne γe c ip ser :
    NonExpansive (λ p, iProto_mapsto γe c ip ser p).
  Proof. rewrite iProto_mapsto_eq. solve_proper. Qed.
  Global Instance iProto_mapsto_proper γe c ip ser
    : Proper ((≡) ==> (≡)) (λ p, iProto_mapsto γe c ip ser p).
  Proof. rewrite iProto_mapsto_eq. solve_proper. Qed.

  Lemma iProto_mapsto_le γe c ip ser p1 p2 :
    c ↣{ γe, ip, ser } p1 -∗ ▷ (p1 ⊑ p2) -∗ c ↣{ γe, ip, ser } p2.
  Proof.
    iIntros "Hc".
    rewrite iProto_mapsto_eq.
    iDestruct "Hc" as (γs s serl serf sa dst) "Hc".
    iDestruct "Hc" as (sbuf slk rbuf rlk ackIdLoc sidLBLoc sidx ridx -> Heqc)
                        "(%Heq1 & Hc)".
    iDestruct "Hc" as "(Hl & %Hsereq & Hsidx & Hridx
                              & #HsT' & #HAddrT & #HsideT & #HidxT
                              & Hp & #Hslk & #Hrlk)".
    iIntros "Hle".
    iExists γs, s, serl, serf, sa, dst.
    iExists sbuf, slk, rbuf, rlk, ackIdLoc, sidLBLoc, sidx, ridx.
    iDestruct (ses_own_le with "Hp Hle") as "Hp". iFrame. iFrame "#". naive_solver.
  Qed.

  Lemma iProto_mapsto_excl γe c ip ser p1 p2 :
    c ↣{ γe, ip, ser } p1 -∗ c ↣{ γe, ip, ser } p2 -∗ False.
  Proof.
    iIntros "Hc".
    rewrite iProto_mapsto_eq.
    iDestruct "Hc" as (γs s serl serf sa dst) "Hc".
    iDestruct "Hc" as (sbuf slk rbuf rlk ackIdLoc sidLBLoc sidx ridx Heqc)
                        "(_ & _ & Hl & _)".
    iIntros "Hc'".
    iDestruct "Hc'" as (γs' s' serl' serf' sa' dst') "Hc'".
    iDestruct "Hc'" as (sbuf' slk' rbuf' rlk' ackIdLoc' sidLBLoc' sidx' ridx' Heqc')
                        "(_ & _ & Hl' & _ )".
    iDestruct "Hl" as  (?) "(Hn & Hl)".
    iDestruct "Hl'" as  (?) "(Hn' & Hl')".
    rewrite Heqc in Heqc'. inversion Heqc'.
    iDestruct (mapsto_node_agree with "Hn Hn'") as "->".
    iDestruct (gen_heap_light.lmapsto_valid_2 serl' (heap_name γn0) 1 1 serf serf'
                with "[$Hl][$Hl']") as "%Habs".
    by rewrite frac_valid in Habs.
  Qed.

End iProto_endpoints.

Notation "c ↣{ γe , ip , ser } p" :=
  (iProto_mapsto γe c ip ser p)
    (at level 20, format "c  ↣{ γe , ip , ser }  p") : bi_scope.
