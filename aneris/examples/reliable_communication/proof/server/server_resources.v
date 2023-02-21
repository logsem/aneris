From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap agree auth numbers frac_auth.
From iris.algebra.lib Require Import excl_auth mono_nat.
From iris.base_logic.lib Require Import invariants mono_nat saved_prop.
From stdpp Require Import namespaces countable.
From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Export serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_code inject.
From aneris.aneris_lang.lib Require Import assert_proof.
From aneris.aneris_lang.lib Require Import lock_proof queue_proof map_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.reliable_communication Require Import user_params.
From aneris.examples.reliable_communication.resources Require Export
     prelude
     chan_session_resources
     chan_endpoints_resources
     socket_interp.

From actris.channel Require Export proto.
From stdpp Require Import base tactics telescopes.

Set Default Proof Using "Type".

Canonical Structure valO := leibnizO val.
Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

Section Server_resources.
  Context `{!anerisG Mdl Σ, !chanG Σ, !lockG Σ}.
  Context `{!Reliable_communication_service_params}.
  Context `{!server_ghost_names}.

  (** Coq predicate modelling the content of the connection map
      for each known client. *)
  Inductive conn_state : Set :=
  | HalfOpened of nat
  | Connected of ((val * nat) * (loc * loc)).

  #[global] Program Instance Inject_conn_state : Inject conn_state val :=
    {| inject a :=
      match a with
      | HalfOpened n => InjLV #n
      | Connected ((ch, ck), (sd, ak)) => InjRV ((ch, #ck)%V, (#sd, #ak)%V)%V
      end
    |}.
  Next Obligation.
    intros x y. simpl.
    destruct x as [nx|((chx, ckx), (akx, sdx))];
      destruct y as [ny|((chy, cky), (aky, sdy))];
      naive_solver.
  Qed.

  #[global] Program Instance Inject_socket_address : Inject socket_address val :=
    {| inject := LitV ∘ LitSocketAddress |}.
  Next Obligation. by intros ?? [=]. Qed.

  Notation srv_ip := (ip_of_address RCParams_srv_saddr).

  (** Connection queue is to be shared between the internal server_listen loop
   and the users's call to accept. *)
  Definition conn_queue_lock_def (qLoc : loc) : iProp Σ :=
    ∃ (qv : val) (vs : list val),
     qLoc ↦[srv_ip] qv ∗ ⌜is_queue vs qv⌝ ∗
     ([∗ list] i ↦ v ∈ vs,
        ∃ (γe : endpoint_name) (c : val) (sa : socket_address),
          ⌜v = (c, #sa)%V⌝ ∗
         (* The fact that we get the initial proto is a bit subtle. *)
          c  ↣{ γe , srv_ip, RCParams_srv_ser } iProto_dual RCParams_protocol ∗
          ChannelAddrToken γe (RCParams_srv_saddr, sa)).

  Definition is_conn_queue_lock γ_qlk qlk qLoc :=
    is_lock
      (RCParams_srv_N .@ "qlk")
      srv_ip γ_qlk qlk (conn_queue_lock_def qLoc).

  (** Server socket predicate defined as a disjunction over whether the listen has been
      already called or not yet. *)
  Definition isServerSocketInternal (srv_skt : val) (listen_flag : bool) : iProp Σ :=
    ∃ (srv_skt_l : loc), ⌜#srv_skt_l = srv_skt⌝ ∗
    ((⌜listen_flag = false⌝ ∗
        ∃ (skt : val) s h,
          srv_skt_l ↦[srv_ip]{1} (InjLV skt) ∗
          isSocket skt s h RCParams_srv_saddr server_interp true Right ∗
            RCParams_srv_saddr ⤳ (∅, ∅) ∗
            known_sessions ∅ ∗
            own γ_srv_known_messages_R_name (● ∅) ∗
            own γ_srv_known_messages_R_name (◯ ∅) ∗
            own γ_srv_known_messages_T_name (● ∅) ∗
            own γ_srv_known_messages_T_name (◯ ∅)) ∨
       (* If the server listen has been invoked, then the isServerSocketInternal only
          keeps the resources relevant for accept, i.e. only about channel queue.
          The ownership over the srv_skt_l makes it exclusive. *)
       (⌜listen_flag = true⌝ ∗
        ∃ γ_qlk qlk (chan_queue_l : loc),
          srv_skt_l ↦[srv_ip]{2/3} (InjRV (#chan_queue_l, qlk)) ∗
          is_conn_queue_lock γ_qlk qlk chan_queue_l)).

  (** The following three definitions describe the resources needed for
      the server listen internal loop. *)

  (** Persistent part of the channel mapsto-connective.
      The server listen loop does not possess the exclusive channel
      mapsto-connectives (which are stored in the connection queue),
      but it still needs to get access to the send and receive lock
      invariants and to get information about meta-tokens as well. *)
  Definition server_endpoint_pers_resources
    γe (c : val)
    (sidLBLoc ackIdLoc : loc) (clt_addr : socket_address) : iProp Σ :=
    ∃ (γs : session_name)
      (sa : socket_address)
      (sbuf : loc) (slk : val)
      (rbuf : loc) (rlk : val),
      ⌜c = ((#sbuf, slk), (#rbuf, rlk))%V⌝ ∗
      ⌜endpoint_chan_name γe = session_chan_name γs⌝ ∗
      ⌜lock_idx_name (endpoint_send_lock_name γe) = (session_srv_idx_name γs)⌝ ∗
      session_token clt_addr γs ∗
      ChannelAddrToken γe (sa, clt_addr) ∗
      ChannelIdxsToken γe (sidLBLoc, ackIdLoc) ∗
      is_send_lock srv_ip
         (endpoint_chan_name γe)
         (endpoint_send_lock_name γe)
         slk sbuf RCParams_srv_ser sidLBLoc Right ∗
      is_recv_lock srv_ip
         (endpoint_chan_name γe)
         (endpoint_recv_lock_name γe)
         rlk rbuf ackIdLoc Right.

  (** The session_map resources state for each known client the following:
   1) there exists a unique session cookie number for which
      the server holds the cookie token authoritative part
      and a persistent session token.
   2) An INIT message has been received, and a INIT-ACK message has been sent.
   3) the connection is either half-opened or established;
      In each of those cases,
      i) the associated logical resources are stored
           - for hal-opened connection: can_init for both ends;
           - for established connection: returned Cookie exclusive token
             and the allocated ackid and seqidLB pointers.
             Additionally, we know that a COOKIE message has been received
             and a reply COOKIE-ACK message has been sent. *)
  Definition session_map_resources sa (st : conn_state) (R T : gset message) : iProp Σ :=
    ∃ (γs : session_name) (n: nat),
      (* --- Common part. --- *)
      (session_token sa γs ∗
      CookieTokenFull sa n ∗
      (* i) received message. *)
        (∃ (m : message) (mval: val), ⌜m ∈ R⌝ ∗
              ⌜s_is_ser (msg_serialization RCParams_clt_ser) mval (m_body m)⌝ ∗
              ⌜m_destination m = RCParams_srv_saddr⌝ ∗
              ⌜m_sender m = sa⌝ ∗
              ⌜mval = InjLV (#"INIT", #0)⌝) ∗
           (* ii) sent message. *)
           (∃ (m' : message) (mval': val), ⌜m' ∈ T⌝ ∗
              ⌜s_is_ser (msg_serialization RCParams_srv_ser) mval' (m_body m')⌝ ∗
              ⌜m_destination m' = sa⌝ ∗
              ⌜m_sender m' = RCParams_srv_saddr⌝ ∗
              ⌜mval' = InjLV (#"INIT-ACK", #n)⌝)) ∗
       (* --- Case analysis. --- *)
        (* Either a connection is half opened. *)
        (* --- the state is half-opened. *)
          ((⌜st = (HalfOpened n)⌝ ∗
            (* iii) resources. *)
            session_half_opened sa γs ∗
            can_init γs sa RCParams_protocol Left ∗
            can_init γs sa (iProto_dual RCParams_protocol) Right)  ∨
          (* --- Or the connection is already established. *)
          (∃ (γc : endpoint_name) (c : val)
             (sidLB_l : loc) (sidLB_n : nat)
             (ackId_l : loc) (ackId_n : nat),
             (* i.2) received COOKIE message. *)
             (∃ (m2 : message) (mval: val), ⌜m2 ∈ R⌝ ∗
              ⌜s_is_ser (msg_serialization RCParams_clt_ser) mval (m_body m2)⌝ ∗
              ⌜m_destination m2 = RCParams_srv_saddr⌝ ∗
              ⌜m_sender m2 = sa⌝ ∗
              ⌜mval = InjLV (#"COOKIE", #n)⌝) ∗
             (* ii) sent message. *)
             (∃ (m' : message) (mval': val), ⌜m' ∈ T⌝ ∗
              ⌜s_is_ser (msg_serialization RCParams_srv_ser) mval' (m_body m')⌝ ∗
              ⌜m_destination m' = sa⌝ ∗
              ⌜m_sender m' = RCParams_srv_saddr⌝ ∗
              ⌜mval' = InjLV (#"COOKIE-ACK", #0)⌝) ∗
              (* the state is established. *)
              ⌜st = (Connected ((c, n), (sidLB_l, ackId_l)))⌝ ∗
              (* iii) resources. *)
               session_connected sa γs ∗
               CookieRes sa n ∗
               sidLB_l ↦[srv_ip]{1/2} #sidLB_n ∗
               ackId_l ↦[srv_ip]{1/2} #ackId_n ∗
               mono_nat_lb_own (session_clt_idx_name γs) ackId_n ∗
               server_endpoint_pers_resources γc c sidLB_l ackId_l sa)).

  (** This definition is used for the first step of the client-server handshake.
      The rationale behind is that the messages other than "INIT" message
      of the client can only arrive if the connection state is in the established
      connection mode. *)
  Definition message_conn_map_resources
    (conn_map_M : gmap socket_address conn_state)
    (m : message) : iProp Σ :=
    ∃ (γs : session_name) (mval : val) (n: nat),
      ⌜s_is_ser (msg_serialization RCParams_clt_ser) mval (m_body m)⌝ ∗
        session_token (m_sender m) γs ∗
        (* Either a connection is half opened. *)
        ((⌜mval = InjLV (#"INIT", #0)⌝ ∗
          ⌜conn_map_M !! (m_sender m) = Some (HalfOpened n)⌝)  ∨
           (* Or the connection is already established. *)
          (∃ (c : val)
             (sidLB_l : loc)
             (ackId_l : loc),
              ⌜conn_map_M !! (m_sender m) =
              Some (Connected ((c, n), (sidLB_l, ackId_l)))⌝
             )).

  (** Putting it all together: resources describing the connection map of the server. *)
  Definition conn_map_resources (conn_map_l : loc) : iProp Σ :=
    ∃ (R T : gset message)
      (conn_map_v : val)
      (γM : session_names_map)
      (conn_map_M : gmap socket_address conn_state),
    (* Coherence between physical and logical maps. *)
    ⌜is_map conn_map_v conn_map_M⌝ ∗
    ⌜dom γM = dom conn_map_M⌝ ∗
    (* Tracking precise knowledge about received messages. *)
    own γ_srv_known_messages_R_name (● R) ∗
    (* Tracking partial knowledge about sent messages. *)
    own γ_srv_known_messages_T_name (◯ T) ∗
    (* Persistent properties over received messages.  *)
    ([∗ set] m ∈ R, ⌜(m_sender m) ∈ dom γM⌝) ∗
    ([∗ set] m ∈ R, message_conn_map_resources conn_map_M m) ∗
    (* Pointer to the connection map. *)
    conn_map_l ↦[srv_ip] conn_map_v ∗
    (* Ghost map storing for known client addresses their session name. *)
    known_sessions γM ∗
    (* Resources for each known client. *)
    ([∗ map] clt_addr ↦ st ∈ conn_map_M, session_map_resources clt_addr st R T).

  (** The ownership describing resources that must hold before and after
      each loop cycle of the server listen (i.e. the definition below is
      a loop invariant of the server_listen function). *)
  Definition isServer_listening_loop_resources srv_skt_passive  : iProp Σ :=
    ∃ (srv_skt_l : loc)
      (skt : val) (conn_map_l : loc)
      (chan_queue_l : loc)
      (qlk : val) (γ_qlk : gname),
      ⌜srv_skt_passive = ((skt, #conn_map_l), (#chan_queue_l, qlk))%V⌝ ∗
      srv_skt_l ↦[srv_ip]{1/3} (InjRV (#chan_queue_l, qlk)) ∗
      (* resources of the connection map *)
      conn_map_resources conn_map_l ∗
      (* socket invariant with message histories and persistent resources *)
      socket_resource skt RCParams_srv_saddr (RCParams_srv_N .@ "skt") Right ∗
      (* resources of the established channel_descr queue  *)
      is_conn_queue_lock γ_qlk qlk chan_queue_l.

  End Server_resources.
