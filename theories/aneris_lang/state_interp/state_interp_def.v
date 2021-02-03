From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
From iris_string_ident Require Import ltac2_string_ident.
From aneris.program_logic Require Export weakestpre adequacy.
From aneris.program_logic Require Import ectx_lifting.
From aneris.program_logic Require Export gen_heap_light.
From aneris.aneris_lang Require Export aneris_lang notation network resources.
From aneris.aneris_lang.lib Require Import util.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.


(* Move these definitions somewhere else *)
Section collect.
  Context {K} `{!EqDecision K} `{Countable K} {A : Type}
          {B : Type} `{!EqDecision B} `{Countable B}
          (f : A → gset B).

  Definition collect (g : gmap K A) : gset B :=
    map_fold (λ _ a acc, (f a) ∪ acc) ∅ g.

  Lemma elem_of_collect g :
    ∀ m, m ∈ collect g ↔ ∃ k a, g !! k = Some a ∧ m ∈ f a.
  Proof.
    pattern (collect g); pattern g.
    match goal with
    |- (λ x, (λ y, ?P) _) _ =>
      simpl; apply (map_fold_ind (M := gmap _) (λ y, λ x, P))
    end.
    - intros m; split; first done.
      intros (?&?&?&?); done.
    - intros k a g' M Hk IHM m.
      split.
      + intros [Hm|Hm]%elem_of_union.
        * exists k, a; rewrite lookup_insert; done.
        * apply IHM in Hm as (k' & a' & Hk' & Hm).
          exists k', a'.
          rewrite lookup_insert_ne; first done.
          set_solver.
      + intros (k' & a' & Hk' & Hm).
        destruct (decide (k' = k)) as [->|].
        * rewrite lookup_insert in Hk'; simplify_eq.
          set_solver.
        * rewrite lookup_insert_ne in Hk'; last done.
          apply elem_of_union; right.
          apply IHM; eauto.
  Qed.

End collect.

Section definitions.
  Context `{anerisG Σ}.
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
  Implicit Types pms : gmap port (message_soup * message_soup).
  Implicit Types mhst :
    gmap ip_address (gmap port (message_soup * message_soup)).
  (* fixme: rename me into mhst *)
  Implicit Types mhγ :
    gmap ip_address (gmap port (message_soup * message_soup)).

  Implicit Types γm : gmap ip_address node_gnames.
  Implicit Types sis : gmap socket_address gname.


  (** Definitions for the message history *)

  (* The set of all received messages *)
  Definition messages_received
      (mh : gmap ip_address (gmap port (message_soup * message_soup))) :=
    collect (λ pms, collect (λ rt, rt.1) pms) mh.

  Lemma elem_of_messages_received mh :
    ∀ m, m ∈ messages_received mh ↔
      ∃ ip Mp port (M : message_soup * message_soup),
        mh !! ip = Some Mp ∧ Mp !! port = Some M ∧ m ∈ M.1.
  Proof.
    intros m; split.
    - intros Hm.
      apply elem_of_collect in Hm as (ip & Mp & HMp1 & HMp2).
      apply elem_of_collect in HMp2 as (port & M & HM1 & HM2); eauto 10.
    - intros (ip & Mp & port & M & HM1 & HM2 & Hm).
      apply elem_of_collect.
      eexists _, _; split; first done.
      apply elem_of_collect; eauto.
  Qed.

  (* The set of all transmitted messages *)
  Definition messages_sent
             (mh : gmap ip_address (gmap port (message_soup * message_soup))) :=
    collect (λ pms, collect (λ rt, rt.2) pms) mh.

  Lemma elem_of_messages_sent mh :
    ∀ m, m ∈ messages_sent mh ↔
      ∃ ip Mp port (M : message_soup * message_soup),
        mh !! ip = Some Mp ∧ Mp !! port = Some M ∧ m ∈ M.2.
  Proof.
    intros m; split.
    - intros Hm.
      apply elem_of_collect in Hm as (ip & Mp & HMp1 & HMp2).
      apply elem_of_collect in HMp2 as (port & M & HM1 & HM2); eauto 10.
    - intros (ip & Mp & port & M & HM1 & HM2 & Hm).
      apply elem_of_collect.
      eexists _, _; split; first done.
      apply elem_of_collect; eauto.
  Qed.

  (* [m] has been received *)
  Definition message_received m mhγ := m ∈ (messages_received mhγ).

  (* Initialization of message history from a given set of ports *)
  Definition messages_init (ports : gset port) :=
    set_fold (fun p macc => <[p := (∅, ∅)]>macc)
             (∅: gmap port (message_soup * message_soup)) ports.

  Definition get_address_messages mhγ sa :=
    match (mhγ !! (ip_of_address sa)) with
    | None => (∅, ∅)
    | Some mps =>
      match mps !! (port_of_address sa) with
      | None => (∅, ∅)
      | Some (R,T) => (R,T)
      end
    end.

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
  Definition gnames_coh γm H S mhγ :=
    dom (gset ip_address) γm = dom (gset ip_address) H ∧
    dom (gset ip_address) γm = dom (gset ip_address) S ∧
    dom (gset ip_address) γm = dom (gset ip_address) mhγ.

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
  Definition message_soup_coh M mhγ :=
    ∀ m, m ∈ M →
         ∃ R T, get_address_messages mhγ (m_sender m) = (R, T) ∧ m ∈ T.

  (* Every message in the receive buffer has been recorded in
     the logic as sent from the node of its origin. *)
  Definition receive_buffers_coh S mhγ :=
    ∀ ip Sn sh skt r m,
      S !! ip = Some Sn →
      Sn !! sh = Some (skt, r) →
      m ∈ r →
      ∃ R T, get_address_messages mhγ (m_sender m) = (R, T) ∧ m ∈ T.

  (* The messages in the logical map mhγ, that tracks
     received and transmitted messages, have coherent addresses. *)
  Definition messages_addresses_coh mhγ :=
    ∀ a R T, get_address_messages mhγ a = (R, T) →
             (∀ m, m ∈ R → m_destination m = a) ∧
             (∀ m, m ∈ T → m_sender m = a).

  Definition messages_received_from_sent_coh mhst :=
    messages_received mhst ⊆ messages_sent mhst.

  Definition messages_received_from_sent_coh_aux mhst :=
    ∀ Mp RT m,
      mhst !! (ip_of_address (m_destination m)) = Some Mp →
      Mp !! (port_of_address (m_destination m)) = Some RT →
      m ∈ RT.1 →
      ∃ Mp' RT',
        mhst !! ip_of_address (m_sender m) = Some Mp' ∧
        Mp' !! port_of_address (m_sender m) = Some RT' ∧
        m ∈ RT'.2.

  Lemma messages_received_from_sent_corrolary_coh mhst :
    messages_addresses_coh mhst →
    messages_received_from_sent_coh mhst →
    messages_received_from_sent_coh_aux mhst.
  Proof.
    intros Hacoh Hrcoh.
    intros Mp RT m HMp HRT Hm.
    assert (m ∈ messages_received mhst) as Hmr.
    { apply elem_of_collect.
      exists (ip_of_address (m_destination m)), Mp.
      split; first done.
      apply elem_of_collect. eauto. }
    apply Hrcoh, elem_of_collect in Hmr as (ip & Mp' & HMp' & Hmt).
    apply elem_of_collect in Hmt as (p & RT' & Hmport & HmRT').
    assert (get_address_messages mhst (SocketAddressInet ip p) =
            (RT'.1, RT'.2)) as Hgas.
    { rewrite /get_address_messages //=. rewrite HMp' Hmport.
      by destruct RT'. }
    specialize
    (Hacoh (SocketAddressInet ip p) RT'.1  RT'.2 Hgas) as (Hc1 & Hc2).
    specialize (Hc2 m HmRT').
    exists Mp', RT'.
      by rewrite Hc2.
  Qed.

    (* Message history is coherent w.r.t.
       message soup, socket map, and itself. *)
  Definition messages_history_coh M S mhγ :=
    message_soup_coh M mhγ ∧
    receive_buffers_coh S mhγ ∧
    messages_addresses_coh mhγ ∧
    messages_received_from_sent_coh mhγ.

 (* For all messages [m] in [M], either the network owns the resources [Φ m]
     described by some socket protocol [Φ] or it has been delivered. *)
  Definition messages_resource_coh mhγ :=
    ([∗ set] m ∈ messages_sent mhγ,
     (* either [m] is governed by a protocol and
        the network owns the resources *)
     (∃ (Φ : socket_interp Σ), (m_destination m) ⤇ Φ ∗ ▷ Φ m) ∨
     (* or [m] has been delivered somewhere *)
     ⌜message_received m mhγ⌝)%I.

  (** State interpretation *)
  Definition aneris_state_interp σ :=
    (∃ γm mhγ,
        ⌜gnames_coh γm (state_heaps σ) (state_sockets σ) mhγ⌝ ∗
        ⌜network_sockets_coh (state_sockets σ) (state_ports_in_use σ)⌝ ∗
        ⌜messages_history_coh (state_ms σ) (state_sockets σ) mhγ⌝ ∗
        node_gnames_auth γm ∗
        socket_interp_coh (state_ports_in_use σ) ∗
        ([∗ map] ip ↦ γs ∈ γm, local_state_coh σ ip γs) ∗
        free_ips_coh σ ∗
        messages_ctx mhγ ∗
        messages_resource_coh mhγ)%I.

End definitions.


Global Instance anerisG_irisG `{!anerisG Σ} : irisG aneris_lang Σ := {
  iris_invG := _;
  state_interp σ κ _ := aneris_state_interp σ;
  fork_post _ := True%I;
}.

Global Opaque iris_invG.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl : core.
Local Hint Constructors head_step : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

(* TODO: come up with something more reliable *)
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
