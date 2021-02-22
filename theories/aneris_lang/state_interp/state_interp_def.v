From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From iris_string_ident Require Import ltac2_string_ident.
From aneris.program_logic Require Export weakestpre adequacy.
From aneris.program_logic Require Import ectx_lifting.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Export aneris_lang notation network resources.
From aneris.aneris_lang.lib Require Import util.
From aneris.aneris_lang.state_interp Require Export messages_history.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Section definitions.
  Context `{anerisG Mdl Σ}.
  Implicit Types σ : state.
  Implicit Types h : heap.
  Implicit Types H : gmap ip_address heap.
  Implicit Types S : gmap ip_address sockets.
  Implicit Types Sn : sockets.
  Implicit Types P : ports_in_use.
  Implicit Types ps : gset port.
  Implicit Types ips : gset ip_address.
  Implicit Types M R T : message_soup.
  Implicit Types m : message.
  Implicit Types a : socket_address.
  Implicit Types ip : ip_address.
  Implicit Types sh : socket_handle.
  Implicit Types skt : socket.
  Implicit Types A B : gset socket_address.
  Implicit Types mh : messages_history.
  Implicit Types rt : message_soup * message_soup.
  Implicit Types γm : gmap ip_address node_gnames.
  Implicit Types sis : gmap socket_address gname.

  (** Local state coherence *)

  (* The local state of the node at [ip] is coherent
     with physical state [σ] and ghost names [γs]. *)
  Definition local_state_coh σ ip γs :=
    (∃ h Sn,
        ⌜state_heaps σ !! ip = Some h⌝ ∗
        ⌜state_sockets σ !! ip = Some Sn⌝ ∗
        mapsto_node ip γs ∗
        heap_ctx γs h ∗
        sockets_ctx γs ((λ x, x.1) <$> Sn))%I.


  (** The domains of heaps and sockets coincide with the gname map [γm] *)
  Definition gnames_coh γm H S mh :=
    dom (gset ip_address) γm = dom (gset ip_address) H ∧
    dom (gset ip_address) γm = dom (gset ip_address) S ∧
    dom (gset ip_address) γm =
    gset_map ip_of_address (dom (gset socket_address) mh).

  (** Socket interpretation coherence *)
  (* Addresses with socket interpretations are bound *)
  Definition socket_interp_coh P :=
    (∃ sis A,
        (* [A] is the set of addresses with fixed interpretations *)
        fixed A ∗
        (* [si] is the map from addresses to name of
           saved socket interpretations *)
        saved_si_auth sis ∗
        (* there exists a socket interpretation for all addresses in this map *)
        ([∗ set] s ∈ (dom (gset socket_address) sis), ∃ φ, s ⤇ φ) ∗
        (* the addresses in A are in the domain of P *)
        ⌜∀ a, a ∈ A → ip_of_address a ∈ dom (gset ip_address) P⌝ ∗
        (* all addresses in [si] either have a fixed interpretation ([a ∈ A]) or
           are dynamically bound. *)
        ⌜∀ a, (ip_of_address a ∈ dom (gset ip_address) P) →
              (a ∈ dom (gset socket_address) sis ↔
                 a ∈ A ∨ (a ∉ A ∧ ∀ ps, P !! ip_of_address a = Some ps →
                                        port_of_address a ∈ ps))⌝)%I.

  (** Free ips coherence *)
  (* Free ips have no bound ports, no heap, and no sockets  *)
  Definition free_ips_coh σ :=
    (∃ free_ips free_ports,
        (* the domains of [free_ips] and [free_ports] are disjoint *)
        (⌜dom (gset _) free_ports ## free_ips ∧
         (* if the ip [ip] is free, no ports have been bound  *)
         (∀ ip, ip ∈ free_ips → state_ports_in_use σ !! ip = Some ∅) ∧
         (* if the ip [ip] is free, neither a heap nor a socket map has been
            allocated *)
         (∀ ip, ip ∈ free_ips →
                state_heaps σ !! ip = None ∧ state_sockets σ !! ip = None) ∧
         (* free ports and bound ports are disjoint *)
         (∀ ip ps, free_ports !! ip = Some (GSet ps) →
             ∃ bound_ports,
               (state_ports_in_use σ) !! ip = Some bound_ports ∧
               ps ## bound_ports )⌝) ∗
         (* we have the auth parts of the resources for free ips and ports *)
         free_ips_auth free_ips ∗
         free_ports_auth free_ports)%I.

  (** Network sockets coherence for bound ports, socket handlers,
      receive buffers, and socket addresses *)
  (* The ports of all bound addresses in [Sn] are also in [P] *)
  Definition bound_ports_coh Sn P :=
    ∀ sh skt a ps r,
      Sn !! sh = Some (skt, r) →
      saddress skt = Some a →
      P !! ip_of_address a = Some ps →
      (port_of_address a) ∈ ps.

  (* All sockets in [Sn] with the same address have the same handler *)
  Definition socket_handlers_coh Sn :=
    ∀ sh sh' skt skt' r r',
      Sn !! sh = Some (skt, r) →
      Sn !! sh' = Some (skt', r') →
      is_Some (saddress skt) →
      saddress skt = saddress skt' →
      sh = sh'.

  (* Sent and received messages at all socket in [Sn] are in [M] *)
  Definition socket_messages_coh Sn :=
    ∀ sh skt r a,
      Sn !! sh = Some (skt, r) →
      saddress skt = Some a →
      ∀ m, m ∈ r → m_destination m = a.

  (* All sockets in [Sn] are bound to ip address [ip] *)
  Definition socket_addresses_coh Sn ip :=
    ∀ sh skt r a,
      Sn !! sh = Some (skt, r) →
      saddress skt = Some a →
      ip_of_address a = ip.

  (* Receive buffers of unbound sockets are empty. *)
  Definition socket_unbound_empty_buf_coh Sn ip :=
    ∀ sh skt r,
      Sn !! sh = Some (skt, r) →
      saddress skt = None →
      r = ∅.

  Definition network_sockets_coh S P :=
    ∀ ip Sn,
      S !! ip = Some Sn →
      bound_ports_coh Sn P ∧
      socket_handlers_coh Sn ∧
      socket_messages_coh Sn ∧
      socket_addresses_coh Sn ip ∧
      socket_unbound_empty_buf_coh Sn ip.

  (** Message history map coherence *)
  (* Every message present in the message soup has been
     recorded in the logic as sent from the node of its origin. *)
  Definition message_soup_coh M mh :=
    ∀ m, m ∈ M → ∃ R T, mh !! (m_sender m) = Some (R, T) ∧ m ∈ T.

  (* Every message in the receive buffer has been recorded in
     the logic as sent from the node of its origin. *)
  Definition receive_buffers_coh S mh :=
    ∀ ip Sn sh skt r m,
      S !! ip = Some Sn →
      Sn !! sh = Some (skt, r) →
      m ∈ r →
      ∃ R T, mh !! (m_sender m) = Some (R, T) ∧ m ∈ T.

  (* Message history is coherent w.r.t.
       message soup, socket map, and itself. *)
  Definition messages_history_coh M S mh :=
    message_soup_coh M mh ∧
    receive_buffers_coh S mh ∧
    messages_addresses_coh mh ∧
    messages_received_from_sent_coh mh.

  (* For all messages [m] in [M], either the network owns the resources [Φ m]
     described by some socket protocol [Φ] or it has been delivered. *)
  Definition messages_resource_coh mh :=
    ([∗ set] m ∈ messages_sent mh,
     (* either [m] is governed by a protocol and
        the network owns the resources *)
     (∃ (Φ : socket_interp Σ), (m_destination m) ⤇ Φ ∗ ▷ Φ m) ∨
     (* or [m] has been delivered somewhere *)
     ⌜message_received m mh⌝)%I.

  (** State interpretation *)
  Definition aneris_state_interp σ mh :=
    (∃ γm,
        ⌜gnames_coh γm (state_heaps σ) (state_sockets σ) mh⌝ ∗
        ⌜network_sockets_coh (state_sockets σ) (state_ports_in_use σ)⌝ ∗
        ⌜messages_history_coh (state_ms σ) (state_sockets σ) mh⌝ ∗
        node_gnames_auth γm ∗
        socket_interp_coh (state_ports_in_use σ) ∗
        ([∗ map] ip ↦ γs ∈ γm, local_state_coh σ ip γs) ∗
        free_ips_coh σ ∗
        messages_ctx mh ∗
        messages_resource_coh mh)%I.

End definitions.

Section Aneris_AS.
  Context `{aG : !anerisG Mdl Σ}.


  Record aneris_aux_state := AnerisAuxState {
    aneris_AS_mhist : messages_history;
    aneris_AS_model : model_state Mdl }.

  Definition get_buffer (S : gmap ip_address sockets) (sa : socket_address)
    : option message_soup :=
    (S !! (ip_of_address sa)) ≫=
    (λ h, (λ x, x.2.2) <$>
       ((find (λ hsr, bool_decide (saddress hsr.2.1 = Some sa)))
          (map_to_list h))).

  (* Lemma get_buffer_correc S sa : *)
  (*   get_buffer S sa = Some M *)

  Definition sent_received_at_evolution (M2 : message_soup)
             (S1 S2 : gmap ip_address sockets)
             (sa : socket_address) (RT : message_soup * message_soup)
    : message_soup * message_soup :=
    default RT
    (get_buffer S1 sa ≫=
     (λ r1, get_buffer S2 sa ≫=
       (λ r2, Some (RT.1 ∪ (r1 ∖ r2), RT.2 ∪ (messages_sent_from sa M2))))).


Definition message_history_evolution (M2 : message_soup)
             (S1 S2 : gmap ip_address sockets) (mh1 : messages_history)
  : messages_history :=
  map_imap (λ sa RT, Some (sent_received_at_evolution M2 S1 S2 sa RT)) mh1.

  Definition user_model_evolution (mdl1 mdl2 : model_state Mdl) :=
    mdl1 = mdl2 ∨ model_rel Mdl mdl1 mdl2.

Program Definition aneris_AS : AuxState aneris_lang :=
  {| aux_state := aneris_aux_state ;
     valid_state_evolution σ1 δ1 κ σ2 δ2 :=
       aneris_AS_mhist δ2 =
       message_history_evolution
         (state_ms σ2)
         (state_sockets σ1) (state_sockets σ2) (aneris_AS_mhist δ1) ∧
       user_model_evolution
         (aneris_AS_model δ1)
         (aneris_AS_model δ2) |}.
Next Obligation.
Proof.
  simpl; intros ??; split.
Admitted.

Lemma aneris_AS_valid_state_evolution_finitary :
  valid_state_evolution_finitary aneris_AS.
Proof.
Admitted.
  (* intros ???. *)
(*   rewrite /valid_state_evolution. simplify_eq /=. *)
(*   intros ?. *)
(*   apply quantifiers.finite_smaller_card_nat. *)
(*   apply finite.sig_finite; last by apply finite.unit_finite. *)
(*   solve_decision. *)
(* Qed. *)

Global Instance anerisG_irisG `{!anerisG Mdl Σ} :
  irisG aneris_lang aneris_AS Σ := {
  iris_invG := _;
  state_interp σ δ _ _ := aneris_state_interp σ (aneris_AS_mhist δ);
  fork_post _ := True%I;
}.

End Aneris_AS.

Global Opaque iris_invG.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl : core.
Local Hint Constructors head_step : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Ltac ddeq k1 k2 :=
  destruct (decide (k1 = k2)); subst;
  repeat
    match goal with
    | Hyp : context[ (<[_:=_]>_) !! _ ] |- _ =>
      rewrite lookup_insert in
          Hyp || (rewrite lookup_insert_ne in Hyp; last done);
      simplify_eq /=
    | Hyp : is_Some _ |- _ => destruct Hyp
    | |- context[ (<[_:=_]>_) !! _ ] =>
      rewrite lookup_insert || (rewrite lookup_insert_ne; last done);
      simplify_eq /=
    |  H1 : ?x = ?z, Heq : ?x = ?y |- _ =>
       rewrite Heq in H1; simplify_eq /=; try eauto
    | Hdel : context[ delete ?n ?m !! ?n = _] |- _ =>
      rewrite lookup_delete in Hdel; simplify_eq /=
    end.
