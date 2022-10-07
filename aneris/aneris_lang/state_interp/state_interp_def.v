From stdpp Require Import fin_maps gmap option finite.
From trillium.prelude Require Import
     quantifiers finitary classical_instances sigma.
From aneris.prelude Require Import collect gset_map gmultiset.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap mono_nat.
From trillium.program_logic Require Import weakestpre adequacy.
From trillium.events Require Import event.
From aneris.aneris_lang Require Import resources events.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Export aneris_lang network resources.
From aneris.aneris_lang.state_interp Require Export messages_history.
From aneris.algebra Require Import disj_gsets.
From iris.algebra Require Import auth.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
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
  Implicit Types M : message_multi_soup.
  Implicit Types R T : message_soup.
  Implicit Types m : message.
  Implicit Types a : socket_address.
  Implicit Types ip : ip_address.
  Implicit Types sh : socket_handle.
  Implicit Types skt : socket.
  Implicit Types A B : gset socket_address_group.
  Implicit Types mhm : messages_history_map.
  Implicit Types rt : message_soup * message_soup.
  Implicit Types γm : gmap ip_address node_gnames.
  Implicit Types sis : gmap socket_address_group gname.

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
  Definition gnames_coh γm H S :=
    dom γm = dom H ∧
    dom γm = dom S.

  Definition sis_own (sags : gset socket_address_group) : iProp Σ :=
    ∃ (sis : gmap socket_address_group gname),
      saved_si_auth sis ∗
      ⌜dom sis = sags⌝ ∗
      [∗ set] sag ∈ sags, ∃ φ, sag ⤇* φ.

  (** Socket interpretation coherence *)
  (* Addresses with socket interpretations are bound *)
  Definition socket_interp_coh sags :=
    (∃ (A : gset socket_address_group),
        ⌜A ⊆ sags⌝ ∗
        socket_address_group_ctx sags ∗
        (* [A] is the set of socket addresses without an interpretation *)
        unallocated_groups_auth A ∗
        (* [sags ∖ A] is the set of addresses with a saved socket interpretation *)
        sis_own (sags ∖ A))%I.

  (** Free ips coherence *)
  (* Free ips have no bound ports, no heap, and no sockets  *)
  Definition free_ips_coh σ :=
    (∃ free_ips free_ports,
        (* the domains of [free_ips] and [free_ports] are disjoint *)
        (⌜dom free_ports ## free_ips ∧
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

  (* The firewall map and state agree on which socket addresses are public *)
  Definition firewall_st_coh (fw_st : gmap socket_address_group firewall_st) (σ : state) : Prop :=
    ∀ sa, sa ∈ (state_public_addrs σ) <-> ∃ sag, sa ∈ sag ∧ fw_st !! sag = Some FirewallStPublic.

  (* Every delivered message that comes from an adversary is delivered
     to a public address *)
  Definition firewall_delivery_coh mhm σ : Prop :=
    ∀ (sag : gset socket_address) R T m,
      mhm !! sag = Some (R, T) ->
      m ∈ R ->
      (ip_of_address (m_sender m)) ∈ (state_adversaries σ) ->
      m_destination m ∈ (state_public_addrs σ).

  (* The adversary map and state agree on which ips are public *)
  Definition adversary_st_coh (adv_st : gmap ip_address bool) σ :=
    (* we track precisely the allocated ips *)
    dom adv_st = dom (state_sockets σ) ∧
    ∀ ip, ip ∈ (state_adversaries σ) <-> adv_st !! ip = Some true.

  (* SAGs are either all public or all private *)
  Definition sags_preserve_adv_state (sags : gset socket_address_group)
                                     (advs : gset ip_address) : Prop :=
    ∀ sag sa1 sa2, sag ∈ sags ->
                   sa1 ∈ sag ->
                   sa2 ∈ sag ->
                   (ip_of_address sa1 ∈ advs <-> ip_of_address sa2 ∈ advs).

  (* Adversary and firewall coherence *)
  Definition adversary_firewall_coh mhm σ sags : iProp Σ :=
    ∃ adv_st fw_st,
      adversary_auth adv_st ∗
      firewall_auth fw_st ∗
      ⌜sags_preserve_adv_state sags (state_adversaries σ)⌝ ∗
      ⌜adversary_st_coh adv_st σ⌝ ∗
      ⌜firewall_st_coh fw_st σ⌝ ∗
      ⌜firewall_delivery_coh mhm σ⌝.

  (** Network sockets coherence for bound ports, socket handlers,
      receive buffers, and socket addresses *)
  (* The ports of all bound addresses in [Sn] are also in [P] *)
  Definition bound_ports_coh Sn P :=
    ∀ sh skt a ps r,
    Sn !! sh = Some (skt, r) →
    saddress skt = Some a →
    P !! ip_of_address a = Some ps →
    port_of_address a ∈ ps.

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
    r = [].

  Definition network_sockets_coh S P :=
    ∀ ip Sn,
    S !! ip = Some Sn →
    bound_ports_coh Sn P ∧
    socket_handlers_coh Sn ∧
    socket_messages_coh Sn ∧
    socket_addresses_coh Sn ip ∧
    socket_unbound_empty_buf_coh Sn ip.

  (* Every message present in the message soup [M] has been recorded in the
     message history [mhm] as sent from the node of its origin. *)
  Definition message_soup_coh M mhm :=
    ∀ m, m ∈ M → ∃ R T sag, (m_sender m) ∈ sag ∧ mhm !! sag = Some (R, T) ∧ m ∈ T.

  (* Every message in the receive buffers of [S] has been recorded in the
     message history [mhm] as sent from the node of its origin. *)
  Definition receive_buffers_coh S mhm :=
    ∀ ip Sn sh skt r m,
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    m ∈ r →
    ∃ R T sag, (m_sender m) ∈ sag ∧ mhm !! sag = Some (R, T) ∧ m ∈ T.

  Definition messages_history_coh M S mhm :=
    message_soup_coh M mhm ∧
    receive_buffers_coh S mhm ∧
    messages_addresses_coh mhm ∧
      messages_received_from_sent_coh mhm.

  (* For all messages in the message history one of the following holds:
     - the network owns the resourced described by some socket protocol
     - the message has been delivered
     - the message was sent by an adversary
     - the message is addressed to an adversary
  *)
 Definition messages_resource_coh mhm : iProp Σ :=
    (* All sets in the domain of [mhm] are disjoint *)
    own (A:=authUR socket_address_groupUR) aneris_socket_address_group_name
        (◯ (DGSets (dom mhm))) ∗
    (* Take the set [ms] of sent messages closed under group equivalence *)
    ∃ ms,
      ⌜ms ⊆ (messages_sent mhm)⌝ ∗
      (* [ms] carries one message, for each message sent by a group in [mhm] *)
      ([∗ set] m ∈ messages_sent mhm,
         (* the message's sender is an adversary... *)
         adversary_saddr_adv_own (m_sender m) ∨
         (* or the receiver is... *)
         adversary_saddr_adv_own (m_destination m) ∨
         (* or the message is between non-adversaries, in which case
            it could carry a spatial resource, so there's a matching message
            in [ms] *)
         ∃ sagT sagR m',
           ⌜m ≡g{sagT,sagR} m' ∧ m' ∈ ms⌝ ∗
           socket_address_group_own sagT ∗
           socket_address_group_own sagR) ∗
      (* For any message [m] in [ms] *)
      ([∗ set] m ∈ ms,
         ∃ sagT sagR Φ,
           (* The group of the message is disjoint, and *)
           ⌜m_destination m ∈ sagR⌝ ∗ sagR ⤇* Φ ∗
           socket_address_group_own sagT ∗
           (* either [m] is governed by a protocol [Φ] and the network owns the
              resources  specified by the protocol *)
           ((∃ m', ⌜m ≡g{sagT,sagR} m'⌝ ∗ ▷ Φ m') ∨
            (* or [m] has been delivered somewhere *)
            (∃ m', ⌜m ≡g{sagT,sagR} m'⌝ ∗ ⌜message_received m' mhm⌝))).

  (** State interpretation *)
  Definition aneris_state_interp σ (rt : messages_history) :=
    (∃ γm mhm sags,
        ⌜messages_received_sent mhm = rt⌝ ∗
        ⌜gnames_coh γm (state_heaps σ) (state_sockets σ)⌝ ∗
        ⌜network_sockets_coh (state_sockets σ) (state_ports_in_use σ)⌝ ∗
        ⌜messages_history_coh (state_ms σ) (state_sockets σ) mhm⌝ ∗
        node_gnames_auth γm ∗
        socket_interp_coh sags ∗
        ([∗ map] ip ↦ γs ∈ γm, local_state_coh σ ip γs) ∗
        free_ips_coh σ ∗
        adversary_firewall_coh mhm σ sags ∗
        messages_ctx mhm ∗
        messages_resource_coh mhm)%I.

  Program Definition aneris_events_state_interp (ex : execution_trace aneris_lang) : iProp Σ :=
    ∃ (As Ar : gset socket_address_group) (lbls : gset string),
      own (A:=authUR socket_address_groupUR) aneris_socket_address_group_name
          (◯ (DGSets (As ∪ Ar))) ∗
      observed_send_groups As ∗ observed_receive_groups Ar ∗
      sendon_evs_ctx (fn_to_gmap As (λ sag, events_of_trace (sendonEV_groups sag) ex)) ∗
      receiveon_evs_ctx (fn_to_gmap Ar (λ sag, events_of_trace (receiveonEV_groups sag) ex)) ∗
      alloc_evs_ctx (fn_to_gmap lbls (λ lbl, events_of_trace (allocEV lbl) ex)).

  Definition buffers (S : gmap ip_address sockets) : message_multi_soup :=
    (multi_collect (λ ip Sn, multi_collect (λ sh sr, list_to_set_disj sr.2) Sn) S).

  Definition message_history_evolution
             (M1 M2 : message_multi_soup)
             (S1 S2 : gmap ip_address sockets)
             (mhm : messages_history) : messages_history :=
    (dom (buffers S1 ∖ buffers S2) ∪ mhm.1, gset_of_gmultiset (M2 ∖ M1) ∪ mhm.2).

  Fixpoint trace_messages_history (ex : execution_trace aneris_lang) : messages_history :=
    match ex with
    | {tr[c]} => (∅, gset_of_gmultiset (state_ms c.2))
    | ex' :tr[_]: c =>
      message_history_evolution
        (state_ms (trace_last ex').2)
        (state_ms c.2)
        (state_sockets (trace_last ex').2)
        (state_sockets c.2)
        (trace_messages_history ex')
    end.

End definitions.

Section Aneris_AS.
  Context `{aG : !anerisG Mdl Σ}.

  Definition user_model_evolution (mdl1 mdl2 : model_state Mdl) :=
    mdl1 = mdl2 ∨ model_rel Mdl mdl1 mdl2.

  Lemma user_model_evolution_id δ :
    user_model_evolution δ δ.
  Proof. by left. Qed.

  Definition valid_state_evolution (_ : execution_trace aneris_lang)
             (atr : auxiliary_trace (aneris_to_trace_model Mdl)) :=
    match atr with
    | atr :tr[_]: δ => user_model_evolution (trace_last atr) δ
    |  _ => True
    end.

  Definition sim_rel (φ : execution_trace aneris_lang → auxiliary_trace (aneris_to_trace_model Mdl) → Prop)
             (ex : execution_trace aneris_lang) (atr : auxiliary_trace (aneris_to_trace_model Mdl)) :=
    valid_state_evolution ex atr ∧ φ ex atr.

  Let M := (aneris_to_trace_model Mdl).

  Local Definition enumerate_next_auxstate (δ : Mdl) (l : list Mdl) : list (M * mlabel M) :=
    δ' ← δ :: l;
    mret (δ', ()).

  Lemma aneris_sim_rel_finitary φ:
    (∀ mdl, smaller_card (sig (λ mdl', model_rel Mdl mdl mdl')) nat) →
    rel_finitary (sim_rel φ).
  Proof.
    intros Hmodel ex atr c oζ.
    specialize (Hmodel (trace_last atr)).

    assert (∀ ex atr x,
     ProofIrrel ((match x return Prop with
                    (δ', ℓ) => (sim_rel φ (ex :tr[ oζ ]: c) (atr :tr[ ℓ ]: δ'))
                  end))).
    { intros ?? []. apply make_proof_irrel. }
    assert (EqDecision (M * mlabel M)).
    { intros ??; apply make_decision. }
    apply finite_smaller_card_nat.
    assert (EqDecision {mdl' : Mdl | Mdl (trace_last atr) mdl'}).
    { intros ??; apply make_decision. }
    apply smaller_card_nat_finite in Hmodel.
    eapply (in_list_finite $ enumerate_next_auxstate (trace_last atr) (map proj1_sig (@enum _ _ Hmodel))).
    intros [δ' []] [[<- | Hstep] _]; unfold enumerate_next_auxstate; simpl; [set_solver |].
    apply elem_of_cons; right. apply elem_of_list_bind. exists δ'; split; first set_solver.
    apply elem_of_list_fmap. exists (δ' ↾ Hstep); split =>//.
    apply elem_of_enum.
  Qed.

  Global Instance anerisG_irisG `{!anerisG Mdl Σ} :
    irisG aneris_lang M Σ := {
    iris_invGS := _;
    state_interp ex atr :=
      (aneris_events_state_interp ex ∗
       aneris_state_interp
         (trace_last ex).2
         (trace_messages_history ex) ∗
       auth_st (trace_last atr) ∗
       ⌜valid_state_evolution ex atr⌝ ∗
       steps_auth (trace_length ex))%I;
    fork_post _ _ := True%I }.

End Aneris_AS.

Global Opaque iris_invGS.

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
