From iris.algebra Require Import auth agree gmap gset list.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export own.
From stdpp Require Export strings decidable coPset gmap mapset pmap sets.
From RecordUpdate Require Import RecordSet.

Module Network.

  (** Basic Network *)
  Definition ip_address := string.

  Definition port := positive.

  (** Socket definitions, subset of POSIX standard. *)
  Inductive address_family :=
  | PF_INET.

  (* Supported socket types. *)
  Inductive socket_type :=
  | SOCK_DGRAM.

  (* Supported protocols. *)
  Inductive protocol :=
  | IPPROTO_UDP.

  Inductive socket_address :=
  | SocketAddressInet (address : ip_address) (port : positive).

  Definition ip_of_address (sa : socket_address) : ip_address :=
    match sa with
    | SocketAddressInet ip _ => ip
    end.
  Definition port_of_address (sa : socket_address) : positive :=
    match sa with
    | SocketAddressInet _ p => p
    end.

  Record socket := Socket {
    sfamily : address_family;
    stype : socket_type;
    sprotocol : protocol;
    saddress : option socket_address
  }.

  Global Instance etaSocket : Settable _ := settable! Socket <sfamily; stype; sprotocol; saddress>.

  Definition socket_handle := positive.

  Global Instance address_family_eq_dec : EqDecision address_family.
  Proof. solve_decision. Defined.

  Global Instance socket_type_eq_dec : EqDecision socket_type.
  Proof. solve_decision. Defined.

  Global Instance protocol_eq_dec : EqDecision protocol.
  Proof. solve_decision. Defined.

  Global Instance socket_address_eq_dec : EqDecision socket_address.
  Proof. solve_decision. Defined.

  Global Instance socket_eq_dec : EqDecision socket.
  Proof.
    intros [[] [] [] o] [[] [] [] o'];
      destruct (decide (o = o'));
      subst; first (by left);
        by (right; intros Heq; inversion Heq; auto).
  Qed.

  Global Instance socket_address_countable : Countable socket_address.
  Proof.
    refine {| encode := λ x,
                        match x with
                          SocketAddressInet a p => encode (a, p)
                        end;
           decode := λ x, match @decode (ip_address * positive) _ _ x with
                          | None => None
                          | Some y => Some (SocketAddressInet (fst y) (snd y))
                          end
           |}.
    { intros []. by rewrite decode_encode. }
  Qed.

  Global Instance address_family_countable : Countable address_family.
  Proof.
    refine {| encode := λ x, 1%positive;
              decode := λ x, Some PF_INET
           |}.
    { by intros []. }
  Qed.

  Global Instance socket_type_countable : Countable socket_type.
  Proof.
    refine {| encode := λ x,
                        match x with
                        | SOCK_DGRAM => 1%positive
                        end;
              decode := λ x,
                        match x with
                        | _ => Some SOCK_DGRAM
                        end
           |}.
    { by intros []. }
  Qed.

  Global Instance protocol_countable : Countable protocol.
  Proof.
    refine {| encode := λ x, 1%positive;
              decode := λ x, Some IPPROTO_UDP
           |}.
    { by intros []. }
  Qed.

  (** Ports in use on the client **)
  Definition node_ports := gmap ip_address coPset.

  (** Messages *)
  Definition message_body := string.

  Record message := Message {
    m_sender : socket_address;
    m_destination : socket_address;
    m_protocol : protocol;
    m_body : message_body;
  }.

  Instance etaMessage : Settable _ := settable! Message <m_sender; m_destination; m_protocol; m_body>.

  Global Instance message_decidable : EqDecision message.
  Proof. solve_decision. Defined.

  Global Instance message_countable : Countable message.
  Proof.
    refine {| encode x :=
                encode (m_sender x, (m_destination x, (m_protocol x, m_body x)));
              decode x :=
                match (decode x) with
                  Some t => Some
                   {| m_sender := t.1;
                      m_destination := t.2.1;
                      m_protocol := t.2.2.1;
                      m_body := t.2.2.2 |}
                | None => None
                end
           |}.
    by intros []; rewrite decode_encode.
  Qed.

  Definition message_soup := gset message.

  Global Instance message_soup_decidable : EqDecision message_soup.
  Proof. solve_decision. Defined.

  Global Instance message_soup_countable : Countable message_soup.
  Proof. apply _. Qed.

  Definition messages_to_receive_at (sa : socket_address) (M : message_soup) :=
    filter (λ (m : message), m_destination m = sa) M.

End Network.
