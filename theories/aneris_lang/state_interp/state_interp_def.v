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

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

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
  Implicit Types mh : gmap socket_address (message_soup * message_soup).
  Implicit Types rt : message_soup * message_soup.
  Implicit Types γm : gmap ip_address node_gnames.
  Implicit Types sis : gmap socket_address gname.


  (** Definitions for the message history *)

  (* The set of all received messages *)
  Definition messages_received mh := collect (λ rt, rt.1) mh.

  Lemma elem_of_messages_received mh :
    ∀ m, m ∈ messages_received mh ↔
      ∃ sa rt, mh !! sa = Some rt ∧ m ∈ rt.1.
  Proof. by apply elem_of_collect; eauto. Qed.

  (* The set of all transmitted messages *)
  Definition messages_sent mh := collect (λ rt, rt.2) mh.

  Lemma elem_of_messages_sent mh :
    ∀ m, m ∈ messages_sent mh ↔
      ∃ sa rt, mh !! sa = Some rt ∧ m ∈ rt.2.
  Proof. by apply elem_of_collect; eauto. Qed.

  (* [m] has been received *)
  Definition message_received m mh := m ∈ (messages_received mh).

  (* Initialization of message history from a given set of ports *)
  Definition history_init ip ports :
    gmap socket_address (message_soup * message_soup) :=
    gset_to_gmap (∅, ∅) (gset_map (λ p, SocketAddressInet ip p) ports).

   Lemma history_init_dom ip ports :
    ports ≠ ∅ →
    gset_map
      ip_of_address
      (gset_map (λ p : positive, SocketAddressInet ip p) ports) =
   {[ip]}.
  Proof.
    induction ports as [| p ports Hp IH] using set_ind_L; first done.
    intros Hu.
    destruct (decide (ports = ∅)) as [->| Hports].
    - rewrite right_id_L.
      assert (ip = ip_of_address (SocketAddressInet ip p)) as -> by done.
        by rewrite !gset_map_singleton.
    - rewrite !gset_map_union. rewrite IH; last done.
      assert (ip = ip_of_address (SocketAddressInet ip p)) as -> by done.
      rewrite !gset_map_singleton. set_solver.
  Qed.

  Lemma history_init_empty ip ports :
    ∀ a r t, history_init ip ports !! a = Some (r, t) ↔
            ip_of_address a = ip ∧ port_of_address a ∈ ports ∧ (r,t) = (∅, ∅).
  Proof.
    intros.
    split.
    - intros Hinit.
      apply lookup_gset_to_gmap_Some in Hinit as (Ha & ->).
      apply gset_map_correct2 in Ha. set_solver.
    - intros (<- & Hp & ->).
      rewrite lookup_gset_to_gmap_Some.
      split; last done.
      induction ports using set_ind_L; first done.
      rewrite gset_map_union.
      destruct (decide (port_of_address a = x)) as [<- | Hneq].
      + rewrite gset_map_singleton.
        apply elem_of_union_l, elem_of_singleton.
        by destruct a.
      + apply elem_of_union_r. set_solver.
  Qed.

  Lemma gset_to_gmap_singleton (v: message_soup * message_soup)
        (a : socket_address) : gset_to_gmap v {[ a ]} = {[a := v]}.
  Proof.
    assert ({[a]} = {[a]} ∪ (∅: gset socket_address)) as -> by by set_solver.
      by rewrite (gset_to_gmap_union_singleton v a ∅) gset_to_gmap_empty.
  Qed.

  Lemma history_init_disj ip ports mh :
    (∀ p : positive, mh !! SocketAddressInet ip p = None) →
    history_init ip ports ##ₘ mh.
  Proof.
    intros Hips.
    rewrite map_disjoint_spec.
    intros sa rt rt' Hi Hmh.
    destruct rt as (r,t).
    erewrite history_init_empty in Hi.
    specialize (Hips (port_of_address sa)).
    destruct Hi as (<- & Hps & ?).
    assert
      (sa = SocketAddressInet (ip_of_address sa) (port_of_address sa))
      as Hsa.
      by destruct sa.
      rewrite -Hsa in Hips. naive_solver.
  Qed.

  Lemma not_elem_of_dom_history ip p
        (mh : gmap socket_address (message_soup * message_soup)) :
    ip ∉ gset_map ip_of_address (dom (gset socket_address) mh) →
    SocketAddressInet ip p ∉ dom (gset socket_address) mh.
  Proof.
    intros Hip Habs.
    apply Hip. clear Hip.
    assert (ip = ip_of_address (SocketAddressInet ip p)) as -> by done.
    rewrite /gset_map.
    apply elem_of_list_to_set.
    apply elem_of_list_fmap_1.
    by apply elem_of_elements.
  Qed.

  Lemma history_init_singleton ip p :
    history_init ip {[p]} = {[ SocketAddressInet ip p := (∅,∅) ]}.
  Proof. by rewrite /history_init gset_map_singleton gset_to_gmap_singleton. Qed.

  Lemma history_init_emptyset ip :
    history_init ip ∅ = ∅.
  Proof. by rewrite /history_init gset_map_empty gset_to_gmap_empty. Qed.

  Lemma history_init_singleton_union ip p ps :
    p ∉ ps →
    history_init ip ({[p]} ∪ ps) = history_init ip ps ∪ history_init ip {[p]}.
  Proof.
    intro Hp.
    rewrite /history_init.
    rewrite gset_map_union.
    rewrite gset_map_singleton.
    rewrite gset_to_gmap_singleton.
    rewrite gset_to_gmap_union_singleton.
    rewrite insert_union_singleton_l.
    apply map_union_comm.
    apply map_disjoint_dom_2.
    rewrite dom_singleton_L.
    rewrite dom_gset_to_gmap.
    set_solver.
  Qed.

  Lemma history_init_sent ip ports :
    messages_sent (history_init ip ports) = ∅.
  Proof.
    rewrite /messages_sent /history_init.
    apply collect_empty_f.
    intros k a Hka.
    erewrite lookup_gset_to_gmap_Some in Hka.
      by  destruct Hka as (? & <-).
  Qed.

  Lemma history_init_received ip ports :
    messages_received (history_init ip ports) = ∅.
  Proof.
    rewrite /messages_received /history_init.
    apply collect_empty_f.
    intros k a Hka.
    erewrite lookup_gset_to_gmap_Some in Hka.
      by  destruct Hka as (? & <-).
  Qed.

Lemma messages_sent_init ip ports mh :
    history_init ip ports ##ₘ mh →
    messages_sent (history_init ip ports ∪ mh) =
    messages_sent mh.
  Proof.
    intros Hdisj.
    rewrite /messages_sent.
    rewrite collect_disjoint_union; last done.
    erewrite history_init_sent.
      by rewrite left_id_L.
  Qed.

  Lemma message_received_init m ip ports mh :
    history_init ip ports ##ₘ mh →
    message_received m mh →
    message_received m (history_init ip ports ∪ mh).
  Proof.
    intros Hdij Hmsg.
    rewrite /message_received /messages_received.
    erewrite collect_disjoint_union; last done.
    set_solver.
  Qed.

   Lemma messages_sent_insert a R T mh :
    messages_sent (<[a:=(R, T)]> mh) = T ∪ messages_sent (delete a mh).
  Proof.
    rewrite /messages_sent.
    apply collect_insert.
  Qed.

  Lemma message_received_insert a msg R T mh :
    message_received msg (<[a:=(R, T)]> mh) ↔
    msg ∈ R ∨ message_received msg (delete a mh).
  Proof.
    rewrite /message_received /messages_received.
    rewrite collect_insert //= elem_of_union //.
  Qed.

  Lemma messages_sent_split a R T mh :
    mh !! a = Some (R, T) →
    messages_sent mh =
    T ∪ messages_sent (delete a mh).
  Proof.
    intros.
    assert (mh = <[a := (R,T)]>mh) as Heq by by rewrite insert_id.
    rewrite {1} Heq.
    apply collect_insert.
  Qed.

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

  (* The messages in the logical map mhγ, that tracks
     received and transmitted messages, have coherent addresses. *)
  Definition messages_addresses_coh mh :=
    ∀ a R T, mh !! a = Some (R, T) →
             (∀ m, m ∈ R → m_destination m = a) ∧
             (∀ m, m ∈ T → m_sender m = a).

  Definition messages_received_from_sent_coh mh :=
    messages_received mh ⊆ messages_sent mh.

  Definition messages_received_from_sent_coh_aux mh :=
    ∀ rt m,
      mh !! (m_destination m) = Some rt →
      m ∈ rt.1 →
      ∃ rt', mh !! (m_sender m) = Some rt' ∧ m ∈ rt'.2.

  Lemma messages_received_from_sent_corrolary_coh mh :
    messages_addresses_coh mh →
    messages_received_from_sent_coh mh →
    messages_received_from_sent_coh_aux mh.
  Proof.
    intros Hacoh Hrcoh.
    intros rt m Hrt Hm.
    assert (m ∈ messages_received mh) as Hmr.
    { by apply elem_of_collect; eauto. }
    apply Hrcoh, elem_of_collect in Hmr as (sa & rt' & Hrt' & Hmt).
    assert (mh !! sa = Some (rt'.1, rt'.2)) as Hgas by by destruct rt'.
    specialize (Hacoh sa rt'.1  rt'.2 Hgas) as (Hc1 & Hc2).
    specialize (Hc2 m Hmt). set_solver.
  Qed.

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
  Definition aneris_state_interp σ :=
    (∃ γm mh,
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

(* TODO: Define me with histories of sent and received messages. *)
Program Definition aneris_AS : AuxState aneris_lang :=
{| aux_state := unit;
   valid_state_evolution σ1 δ1 κ σ2 δ2 := δ1 = δ2; |}.
Next Obligation.
Proof. done. Qed.

(* TODO: Prove me with histories of sent and received messages. *)
Lemma aneris_AS_valid_state_evolution_finitary :
  valid_state_evolution_finitary aneris_AS.
Proof.
  intros ???.
  rewrite /valid_state_evolution. simplify_eq /=.
  intros ?.
  apply quantifiers.finite_smaller_card_nat.
  apply finite.sig_finite; last by apply finite.unit_finite.
  solve_decision.
Qed.

Global Instance anerisG_irisG `{!anerisG Σ} : irisG aneris_lang aneris_AS Σ := {
  iris_invG := _;
  state_interp σ _ _ _ := aneris_state_interp σ;
  fork_post _ := True%I;
}.

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

Lemma messages_sent_dijsoint a R T mh :
    mh !! a = Some (R, T) →
    messages_addresses_coh mh →
    T ## messages_sent (delete a mh).
  Proof.
    intros Ha Hmcoh.
    apply elem_of_disjoint.
    intros m HmT Hms.
    apply elem_of_collect in Hms as (a' & (R',T') & Ha' & Ht).
    simplify_map_eq.
    destruct (Hmcoh a R T Ha) as (_ & HT).
    specialize (HT m HmT).
    rewrite -HT in Ha'.
    ddeq a' (m_sender m).
    rewrite lookup_delete_ne in Ha'; last done.
    destruct (Hmcoh a' R' T' Ha') as (_ & HT').
    specialize (HT' m Ht).
    done.
  Qed.
