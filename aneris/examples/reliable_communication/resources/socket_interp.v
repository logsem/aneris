From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap agree auth numbers frac_auth.
From iris.algebra.lib Require Import excl_auth mono_nat.
From iris.base_logic.lib Require Import invariants mono_nat saved_prop.
From stdpp Require Import namespaces countable.
From aneris.prelude Require Import strings.
From aneris.aneris_lang.lib.serialization Require Export serialization_proof.
From aneris.aneris_lang Require Import proofmode resources.
From aneris.examples.reliable_communication Require Import user_params.
From aneris.examples.reliable_communication.resources Require Import chan_session_resources.

(** Socket Interpretation. *)
Section SocketInterp.
  Context `{!anerisG Mdl Σ, !chanG Σ, !server_ghost_names}.
  Context `{!Reliable_communication_service_params}.

  (* ------------------------------------------------------------------------- *)
  (** Persistent components of the resources transferred over the network. *)
  (* ------------------------------------------------------------------------- *)

  (** Initialization persistent resources. *)
  (** If the side is Right, then the sender is the client, in which case, the server
     must always receive a session token starting from the 2nd step of the connection. *)
  Definition init_interp_pers clt_addr (str : string) (s : side) (i : nat) : iProp Σ :=
    match s with
      Left => (⌜str = "INIT-ACK"⌝   ∗ ∃ (γs : session_name), session_token clt_addr γs) ∨
             (⌜str = "COOKIE-ACK"⌝ ∗ ∃ (γs : session_name), session_connected clt_addr γs)
    | Right =>
       (⌜str = "INIT"⌝ ∗ ⌜i = 0⌝) ∨
       (⌜str = "COOKIE"⌝ ∗ ∃ (γs : session_name), session_token clt_addr γs)
    end.

  (** Sequence id persistent resources. *)
  Definition idmsg_interp_pers clt_addr (i : nat) (v : val) (s : side) : iProp Σ :=
    ∃ (γs : session_name),
      session_token clt_addr γs ∗
      ses_idx (chan_session_escrow_name (session_chan_name γs)) (dual_side s) i v ∗
      mono_nat_lb_own (side_elim s (session_srv_idx_name γs)
                                   (session_clt_idx_name γs)) (i+1).

   (** Acknowledgement persistent resources. *)
  Definition ack_interp_pers clt_addr (i : nat) (s : side) : iProp Σ :=
    ∃ (γs : session_name),
      session_token clt_addr γs ∗
      mono_nat_lb_own (side_elim s (session_clt_idx_name γs)
                                   (session_srv_idx_name γs)) i.


  (* ------------------------------------------------------------------------- *)
  (** Client socket interpretation. *)
  (* ------------------------------------------------------------------------- *)

  Definition client_init_interp clt_addr (s : string) (n : nat) : iProp Σ :=
      (⌜s = "INIT-ACK"⌝ ∗ CookieRes clt_addr n) ∨
      (⌜s = "COOKIE-ACK"⌝ ∗ ∃ γs, can_init γs clt_addr RCParams_protocol Left ∗
                                 session_connected clt_addr γs).

  Definition client_interp : message → iProp Σ :=
    λ m, (∃ (mval : val),
       ⌜(m_sender m) = RCParams_srv_saddr⌝ ∗
       ⌜(s_is_ser (msg_serialization RCParams_srv_ser)) mval (m_body m)⌝ ∗
       ((∃ s i, ⌜mval = InjLV (#(LitString s), #(LitInt i))⌝ ∗
                ∃ (n : nat) (γs : session_name), ⌜Z.of_nat n = i⌝ ∗
                             session_token (m_destination m) γs ∗
                             client_init_interp (m_destination m) s n) ∨
        ((∃ γs, session_connected (m_destination m) γs) ∗
          ((∃ ackid, ⌜mval = InjRV (InjLV ackid)⌝ ∗
                    ∃ (n : nat), ⌜ackid = #n⌝ ∗
                                 ack_interp_pers (m_destination m) n Left) ∨
          (∃ i w, ⌜mval = InjRV (InjRV (#(LitInt i), w))⌝ ∗
                  ∃ (n : nat), ⌜Z.of_nat n = i⌝ ∗
                               idmsg_interp_pers (m_destination m) n w Left)))))%I.

  (* ------------------------------------------------------------------------- *)
  (** Server socket interpretation. *)
  (* ------------------------------------------------------------------------- *)

  Definition server_init_interp
             (clt_addr : socket_address)
             (s r : string) (i : nat)  : iProp Σ :=
    (* INIT PHASE *)
    (⌜s = "INIT"⌝ ∗ ⌜r = "INIT-ACK"⌝ ∗ ⌜i = 0⌝ ∗
       (∀ (m' : message),
          (∃ (cookie : nat) (γs: session_name),
           ⌜s_is_ser
            (msg_serialization RCParams_srv_ser)
            (InjLV (#r, #cookie)%V) (m_body m')⌝ ∗
           ⌜m_sender m' = RCParams_srv_saddr⌝ ∗
           ⌜m_destination m' = clt_addr⌝ ∗
           session_token clt_addr γs ∗
           CookieRes clt_addr cookie) -∗
           client_interp m')) ∨
    (* COOKIE PHASE *)
    (⌜s = "COOKIE"⌝ ∗ ⌜r = "COOKIE-ACK"⌝ ∗
     CookieRes clt_addr i ∗
     (∃ (γs: session_name), session_token clt_addr γs) ∗
       (∀ (m' : message) (n : nat),
          (∃ (γs: session_name),
              ⌜s_is_ser (msg_serialization RCParams_srv_ser)
               (InjLV (#r, #n)%V) (m_body m')⌝ ∗
             ⌜m_sender m' = RCParams_srv_saddr⌝ ∗
             ⌜m_destination m' = clt_addr⌝ ∗
             session_token clt_addr γs ∗
             session_connected clt_addr γs ∗
             can_init γs clt_addr RCParams_protocol Left) -∗
             client_interp m')).

  Definition server_interp : message → iProp Σ :=
    λ m, (∃ (mval : val),
       ⌜(s_is_ser (msg_serialization RCParams_clt_ser)) mval (m_body m)⌝ ∗
       (m_sender m) ⤇ client_interp ∗
       ((∃ s r i, ⌜mval = InjLV (#(LitString s), #(LitInt i))⌝ ∗
                  ∃ (n : nat), ⌜Z.of_nat n = i⌝ ∗
                               server_init_interp (m_sender m) s r n) ∨
          ((∃ γs, session_connected (m_sender m) γs) ∗
             ((∃ ackid, ⌜mval = InjRV (InjLV ackid)⌝ ∗
                    ∃ (n : nat), ⌜ackid = #n⌝ ∗ ack_interp_pers (m_sender m) n Right) ∨
          (∃ i w, ⌜mval = InjRV (InjRV (#(LitInt i), w))⌝ ∗
                  ∃ (n : nat), ⌜Z.of_nat n = i⌝ ∗
                               idmsg_interp_pers (m_sender m) n w Right)))))%I.

  (** Persistent resources transferred over the network. *)
  Definition client_server_interp_pers (s : side) : message → iProp Σ :=
    λ m, (∃ (mval : val),
      (match s with
         Left => ⌜(m_sender m) = RCParams_srv_saddr⌝
       | Right =>  (m_sender m) ⤇ client_interp
       end) ∗
      ⌜(s_is_ser (msg_serialization
          (side_elim s RCParams_srv_ser RCParams_clt_ser)))
            mval (m_body m)⌝ ∗
      ((∃ str (i: nat),
           ⌜mval = InjLV (#(LitString str), #(LitInt i))⌝ ∗
             init_interp_pers (side_elim s (m_destination m) (m_sender m)) str s i) ∨
       ((∃ γs, session_connected (side_elim s (m_destination m) (m_sender m)) γs) ∗
          ((∃ ackid,
           ⌜mval = InjRV (InjLV ackid)⌝ ∗
           ∃ (n : nat), ⌜ackid = #n⌝ ∗
                        ack_interp_pers
                          (side_elim s (m_destination m) (m_sender m)) n s) ∨
       (∃ i w,
           ⌜mval = InjRV (InjRV (#(LitInt i), w)%V)⌝ ∗
           ∃ n : nat, ⌜Z.of_nat n = i⌝ ∗
                      idmsg_interp_pers
                        (side_elim s (m_destination m) (m_sender m)) n w s)))))%I.

  Global Instance client_server_interp_pers_persistent s m :
    Persistent (client_server_interp_pers s m).
  Proof. destruct s; apply _. Qed.

  (** We can always obtain the persistent part of the network resources. *)
  Lemma client_interp_le m :
    client_interp m -∗ client_server_interp_pers Left m.
  Proof.
    iDestruct 1 as (mval Heq Hser) "H".
    iExists mval. iSplit; [done|]. iSplit; [done|].
    iDestruct "H" as "[H | H]".
    { iDestruct "H" as (s i ->) "H". iLeft; simpl.
      iDestruct "H" as (n γs Hn) "(#Hs & [(-> & H)|(-> & (%y & H1 & H2))])"; subst; eauto.
      - iExists _, _. iSplit; [done|]. iLeft. eauto.
      - iExists _, _. iSplit; eauto. }
    iDestruct "H" as "(Hmd & [H | H])".
    { iDestruct "H" as (ackid) "[-> [%n [-> H]]]". iRight. subst; iSplit; first subst; eauto.
      iLeft. iExists _.
      iSplit; [done|]. iExists _. by iFrame. }
    iDestruct "H" as (i w ->) "H".
    iRight. iSplit; first done. iRight. iExists _, _. iSplit; done.
  Qed.

  Lemma server_interp_le m :
    server_interp m -∗ client_server_interp_pers Right m.
  Proof.
    iDestruct 1 as (mval Hser) "[Hinterp H]".
    iExists mval. iSplit; first eauto.
    iSplit; [done|].
    iDestruct "H" as "[H | H]".
    { iDestruct "H" as (s r i ->) "H". iLeft; simpl.
      iDestruct "H" as (n Hn) "[( -> & -> & -> & Hasn)|(-> & -> & Hck & (%γs & Hγs) & H)]".
      - iExists "INIT", _. subst; eauto.
      - iExists "COOKIE", n. iSplit; first subst; eauto. }
    iDestruct "H" as "(Hmd & [H | H])".
    { iDestruct "H" as (ackid) "[-> [%n [-> H]]]". iRight. iSplit; first done.
      iLeft. iExists _.
      iSplit; [done|]. iExists _. by iFrame. }
    iDestruct "H" as (i w ->) "H".
    iRight. iSplit; first done. iRight. iExists _, _. iSplit; done.
  Qed.

  (* ------------------------------------------------------------------------- *)
  (** Resources related to the socket and socket addresses. *)
  (* ------------------------------------------------------------------------- *)

  Definition is_skt_val (skt : val) (sh : socket_handle) (s: side) : iProp Σ :=
    ⌜skt = ((#(LitSocket sh),
                (side_elim s (s_ser (s_serializer (msg_serialization RCParams_clt_ser)))
                             (s_ser (s_serializer (msg_serialization RCParams_srv_ser))),
                 side_elim s (s_deser (s_serializer (msg_serialization RCParams_srv_ser)))
                             (s_deser (s_serializer (msg_serialization RCParams_clt_ser))))),
          side_elim s (s_ser (s_serializer RCParams_clt_ser))
                      (s_ser (s_serializer RCParams_srv_ser)))%V⌝.

  (** In the definition below, for the server side we are tracking message histories
      in the following way:
      1) the resource `(∃ R0, ⌜R ⊆ R0⌝ ∗ own γ_srv_known_messages_R_name (◯ R0))`
         states that the received messages are tracked precisely _outside_ the
         socket resource invariant, by the server listen loop.
         Therefore, every time we receive a new fresh message m,
         the resource `own γ_srv_known_messages_R_name R0` must be updated accordingly.
         This is needed to know that the domain of the session map
         (associating session names to client addresses) is precisely the set of
         "INIT" messages from distinct clients;
      2) the resource `(∃ T0, ⌜T0 ⊆ T⌝ ∗ own γ_srv_known_messages_T_name (● T0))`
         states that on the contrary the sent messages are tracked precisely by
         the socket resources, but there is actually a distinguished subset of
         messages T0 in T, which can be updated whenever a new message is sent.
         Howevef, doing this update is possible, but not necessary.
         Every time the update is performed, a duplicable snapshot
         `own γ_srv_known_messages_T_name (◯ {[m]} ∪ T0))` can be generated
         as a certificate that the message m has been sent indeed.
         Thus, knowing that a message is in the set T0 allows to resend it
         without providing resources specified by the destination protocol.
         This is useful to encode that if the connection state for a given client
         is half-opened, then "INIT-ACK" has been already sent.
         Similarly, if the connection state for a given client is in the established mode,
         then "COOKIE-ACK" has benn already sent. *)
  Definition socket_inv_def sh sa sock s : iProp Σ :=
    (∃ (R T : message_soup),
              sh ↪[ip_of_address sa] sock ∗ sa ⤳ (R, T) ∗
              (side_elim s True (∃ R0, ⌜R ⊆ R0⌝ ∗ own γ_srv_known_messages_R_name (◯ R0))) ∗
              (side_elim s True (∃ T0, ⌜T0 ⊆ T⌝ ∗ own γ_srv_known_messages_T_name (● T0))) ∗
              [∗ set] m ∈ R, client_server_interp_pers s m).

  (** This definition is common for client and server, as the channel ghost name
   for the fraglists is existentially quantified in the idmsg_interp but is tied
   via the session_token clt_addr γ *)
  Definition socket_resource
    (skt : val) (sa : socket_address) (N : namespace) (s : side) : iProp Σ :=
    ∃ (sh : socket_handle) (sock : socket),
      is_skt_val skt sh s ∗
      ⌜saddress sock = Some sa⌝ ∗
      ⌜sblock sock = true⌝ ∗
      sa ⤇ side_elim s client_interp server_interp ∗
      inv N (socket_inv_def sh sa sock s).

  Definition isSocket skt h s sa ϕ bflag (sd : side) : iProp Σ :=
    is_skt_val skt h sd ∗
    ⌜saddress s = Some sa⌝ ∗
    ⌜sblock s = bflag⌝ ∗
    h ↪[ip_of_address sa] s ∗
    sa ⤇ ϕ.

  Global Instance serInit (str: string) (n : nat) (s: side) :
    Serializable (msg_serialization
                    (side_elim s RCParams_clt_ser RCParams_srv_ser))
                 (InjLV (#str, #n%nat)).
  Proof. exists (#str, #n)%V. left. split; first eauto; simpl.
         do 2 eexists; split; first done. split; by eexists.
  Qed.

  Lemma msg_ser_is_ser_injective s :
    ser_is_injective (msg_serialization
                        (side_elim s RCParams_clt_ser RCParams_srv_ser)).
  Proof.
    apply sum_ser_is_ser_injective.
    - apply prod_ser_is_ser_injective.
      + apply string_ser_is_ser_injective.
      + apply int_ser_is_ser_injective.
    - apply sum_ser_is_ser_injective.
      + apply int_ser_is_ser_injective.
      + apply prod_ser_is_ser_injective.
        * apply int_ser_is_ser_injective.
        * intros str mval1 mval2 Hs1 Hs2.
          destruct s; [by eapply RCParams_clt_ser_inj|
                        by eapply RCParams_srv_ser_inj].
  Qed.

  Lemma msg_ser_is_ser_injective_alt s :
    ser_is_injective_alt (msg_serialization
                        (side_elim s RCParams_clt_ser RCParams_srv_ser)).
  Proof.
    apply sum_ser_is_ser_injective_alt.
    - apply prod_ser_is_ser_injective_alt.
      + apply string_ser_is_ser_injective_alt.
      + apply int_ser_is_ser_injective_alt.
    - apply sum_ser_is_ser_injective_alt.
      + apply int_ser_is_ser_injective_alt.
      + apply prod_ser_is_ser_injective_alt.
        * apply int_ser_is_ser_injective_alt.
        * intros str mval1 mval2 Hs1 Hs2.
          destruct s; [by eapply RCParams_clt_ser_inj_alt|
                        by eapply RCParams_srv_ser_inj_alt].
  Qed.

End SocketInterp.
