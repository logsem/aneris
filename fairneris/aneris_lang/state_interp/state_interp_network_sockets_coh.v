From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From fairneris.lib Require Import gen_heap_light.
From fairneris.aneris_lang Require Import
     aneris_lang network resources.
From fairneris.aneris_lang.state_interp Require Import
     state_interp_def.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  (** bound_ports_coh *)
  Lemma bound_ports_coh_alloc_socket Sn P sh skt :
    Sn !! sh = None →
    saddress skt = None →
    bound_ports_coh Sn P →
    bound_ports_coh (<[sh:=(skt, [])]> Sn) P.
  Proof.
    intros ??? sh' ???? Hup.
    destruct (decide (sh = sh')) as [Heq|];
      simplify_map_eq.
    - rewrite lookup_insert in Hup. simplify_eq /=.
      intros. simplify_eq /=.
    - rewrite lookup_insert_ne in Hup; eauto.
  Qed.

  Lemma bound_ports_coh_socketbind P Sn ps sh skt a :
    let Sn' := (<[sh:=(skt <| saddress := Some a |>, [])]> Sn) in
    let P' := (<[ip_of_address a:={[port_of_address a]} ∪ ps]> P) in
    P !! ip_of_address a = Some ps →
    bound_ports_coh Sn P →
    bound_ports_coh Sn' P'.
  Proof.
    rewrite /bound_ports_coh /=.
    intros HP HbpsCoh sh' skt' a' P' r' Hsh' Hskt' HP'.
    destruct (decide (sh' = sh)); simplify_map_eq.
    - rewrite lookup_insert in Hsh'; simplify_map_eq.
      rewrite lookup_insert in HP'; by set_solver.
    - rewrite lookup_insert_ne // in Hsh'.
      destruct (decide ((ip_of_address a') = (ip_of_address a)))
        as [Heq|]; simplify_map_eq.
      + destruct Heq.
        rewrite lookup_insert in HP'. simplify_eq /=.
        destruct (decide (port_of_address a' = port_of_address a));
          [set_solver|].
        apply elem_of_union_r. by eapply HbpsCoh.
      + rewrite lookup_insert_ne in HP'; [|done].
        by eapply HbpsCoh.
  Qed.

  Lemma bound_ports_coh_receive
        P (S : gmap ip_address sockets) Sn ip sh skt r m :
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r ++ [m]) →
    bound_ports_coh Sn P →
    bound_ports_coh (<[sh:=(skt, r)]> Sn) P.
  Proof.
    rewrite /bound_ports_coh /=.
    intros HS HSn HbpsCoh sh' skt' a' P' r' Hsh' Hskt' HP'.
    ddeq sh sh'; eapply HbpsCoh; eauto.
  Qed.

  Lemma bound_ports_coh_update_sblock σ Sn ip sh skt r b :
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    bound_ports_coh Sn (state_ports_in_use σ) →
    bound_ports_coh
      (<[sh:=({| saddress := saddress skt;
                 sblock := b |}, r)]> Sn)
      (state_ports_in_use σ).
  Proof.
    rewrite /bound_ports_coh /=.
    intros HS HSn HbpsCoh sh' skt' a' P' r' Hsh' Hskt' HP'.
    ddeq sh sh'; eapply HbpsCoh; eauto.
  Qed.

  Lemma bound_ports_coh_deliver_message M P Sn sh skt a R m :
    m ∈ messages_to_receive_at a M →
    Sn !! sh = Some (skt, R) →
    saddress skt = Some a →
    bound_ports_coh Sn P →
    bound_ports_coh (<[sh:=(skt, m::R)]> Sn) P.
  Proof.
    rewrite /bound_ports_coh; intros HM HSh Hskt HSn.
    intros sh' skt' a' ps r Hsh' Hskt' HP.
    destruct (decide (sh = sh')) as [->|].
    - rewrite lookup_insert in Hsh'; simplify_eq; eauto.
    - rewrite lookup_insert_ne in Hsh'; last done. simplify_eq; eauto.
  Qed.

  (** socket_handlers_coh *)
  Lemma socket_handlers_coh_alloc_socket Sn sh s :
    saddress s = None →
    socket_handlers_coh Sn →
    socket_handlers_coh (<[sh:=(s, [])]> Sn).
  Proof.
    intros ?? sh1 sh2 * ??? H. symmetry in H.
    ddeq sh1 sh2; ddeq sh1 sh; ddeq sh2 sh; eauto.
  Qed.

  Lemma socket_handlers_coh_socketbind Sn sh skt a :
    (∀ sh' skt' r' a',
       Sn !! sh' = Some (skt', r') →
       saddress skt' = Some a' →
       port_of_address a' ≠ port_of_address a) →
    socket_handlers_coh Sn →
    socket_handlers_coh (<[sh:=(skt <| saddress := Some a |>, [])]> Sn).
  Proof.
    intros ? Hscoh sh1 sh2 skt1 skt2 ????? Heq.
    ddeq sh1 sh; ddeq sh2 sh; simplify_eq=>//.
    - destruct skt, skt2; simplify_map_eq. set_solver.
    - destruct skt, skt1. simplify_map_eq. set_solver.
    - destruct skt1, skt2. simplify_map_eq. eapply Hscoh; eauto.
  Qed.

  Lemma socket_handlers_coh_receive Sn sh skt r m :
    Sn !! sh = Some (skt, r ++ [m]) →
    socket_handlers_coh Sn →
    socket_handlers_coh (<[sh:=(skt, r)]> Sn).
  Proof.
    intros ? Hscoh sh1 sh2 skt1 skt2 ????? Heq.
    ddeq sh1 sh; ddeq sh2 sh; simplify_eq=>//.
    - naive_solver.
    - eapply Hscoh; eauto. rewrite Heq. eauto.
    - eapply Hscoh; eauto. rewrite Heq. eauto.
  Qed.

  Lemma socket_handlers_coh_deliver_message M Sn sh skt a R m :
    m ∈ messages_to_receive_at a M →
    Sn !! sh = Some (skt, R) →
    saddress skt = Some a →
    socket_handlers_coh Sn  →
    socket_handlers_coh (<[sh:=(skt, m :: R)]> Sn).
  Proof.
    intros HM Hsh Hskt HSn sh1 sh2 skt1 skt2 r1 r2 Hsh1 Hsh2 Hskt1 Hskt12.
    destruct (decide (sh1 = sh)) as [->|];
      destruct (decide (sh2 = sh)) as [->|]; simplify_eq; eauto.
    - rewrite lookup_insert in Hsh1; rewrite lookup_insert_ne in Hsh2;
        last done.
      eapply HSn; eauto; naive_solver.
    - rewrite lookup_insert_ne in Hsh1; last done;
        rewrite lookup_insert in Hsh2.
      eapply HSn; eauto; naive_solver.
    - rewrite lookup_insert_ne in Hsh1; last done;
        rewrite lookup_insert_ne in Hsh2; last done.
      eapply HSn; eauto; naive_solver.
  Qed.

  Lemma socket_handlers_coh_update_sblock σ Sn ip sh skt r b :
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    socket_handlers_coh Sn  →
    socket_handlers_coh
      (<[sh:=({| saddress := saddress skt;
                 sblock := b |}, r)]> Sn).
  Proof.
    intros ?? Hscoh sh1 sh2 skt1 skt2 ????? Heq.
    ddeq sh1 sh; ddeq sh2 sh; simplify_eq=>//.
    - eapply Hscoh; eauto. by rewrite Heq in H1.
    - eapply Hscoh; eauto. rewrite Heq. eauto.
    - eapply Hscoh; eauto. rewrite Heq. naive_solver.
  Qed.

  (** socket_messages_coh *)
  Lemma socket_messages_coh_update_socket Sn sh skt :
    socket_messages_coh Sn →
    socket_messages_coh (<[sh:=(skt, [])]> Sn).
  Proof. intros ? sh' **. ddeq sh sh'; [set_solver|]. eauto. Qed.

  Lemma socket_messages_coh_insert_received a sh skt m r Sn :
    Sn !! sh = Some (skt, r) →
    m_destination m = a →
    saddress skt = Some a →
    socket_messages_coh Sn →
    socket_messages_coh (<[sh:=(skt, m :: r)]> Sn).
  Proof.
    intros ??? Hmcoh sh' skt' r' a' Hsh' ?.
    destruct (decide (sh = sh')); simplify_eq; last first.
    { rewrite lookup_insert_ne // in Hsh'. by eapply Hmcoh. }
    rewrite lookup_insert in Hsh'; simplify_eq.
    intros m' [HR | ?] %elem_of_cons; subst; [done|].
    by eapply Hmcoh.
  Qed.

  Lemma socket_messages_coh_deliver_message M Sn sh skt a R m :
    m ∈ messages_to_receive_at a M →
    Sn !! sh = Some (skt, R) →
    saddress skt = Some a →
    socket_messages_coh Sn →
    socket_messages_coh (<[sh:=(skt, m :: R)]> Sn).
  Proof.
    intros HM Hsh Hskt HSn sh' kt' r' a' Hsh' Hskt'.
    destruct (decide (sh = sh')); simplify_eq; last first.
    { rewrite lookup_insert_ne // in Hsh'. by eapply HSn. }
    rewrite lookup_insert in Hsh'; simplify_eq.
    intros m' [HR | ?]%elem_of_cons; subst.
    - apply elem_of_filter in HM as [? ?]; done.
    - by eapply HSn.
  Qed.

  Lemma socket_messages_coh_receive Sn sh skt r m :
    Sn !! sh = Some (skt, r ++ [m]) →
    socket_messages_coh Sn →
    socket_messages_coh (<[sh:=(skt, r)]> Sn).
  Proof.
    intros HSn Hcoh sh' kt' r' a' Hsh' Hskt' m' Hm'.
    ddeq sh sh'; eapply Hcoh; eauto.
    ddeq m m'; set_solver.
  Qed.

  Lemma socket_messages_coh_update_sblock Sn sh skt r b:
    Sn !! sh = Some (skt, r) →
    socket_messages_coh Sn →
    socket_messages_coh   (<[sh:=({| saddress := saddress skt;
                                     sblock := b |}, r)]> Sn).
  Proof.
    intros HSn Hcoh sh' kt' r' a' Hsh' Hskt' m' Hm'.
    ddeq sh sh'; eapply Hcoh; eauto.
  Qed.

  (** socket_addresses_coh *)
  Lemma socket_addresses_coh_alloc_socket Sn sh skt n :
    saddress skt = None →
    socket_addresses_coh Sn n →
    socket_addresses_coh (<[sh:=(skt, [])]> Sn) n.
  Proof. intros ? ? sh' **. ddeq sh' sh; eauto. Qed.

  Lemma socket_addresses_coh_socketbind Sn sh skt a :
    saddress skt = None →
    socket_addresses_coh Sn (ip_of_address a) →
    socket_addresses_coh
      (<[sh:=(skt <| saddress := Some a |>, [])]> Sn) (ip_of_address a).
  Proof. intros ? ? sh' **; ddeq sh sh'; eauto. Qed.

  Lemma socket_addresses_coh_insert_received sh a skt m R Sn :
    saddress skt = Some a →
    socket_addresses_coh Sn (ip_of_address a) →
    socket_addresses_coh (<[sh:=(skt, m :: R)]> Sn) (ip_of_address a).
  Proof. intros ?? sh' **; ddeq sh sh'; eauto. Qed.

  Lemma socket_addresses_coh_deliver_message M Sn sh ip skt a R m :
    m ∈ messages_to_receive_at a M →
    Sn !! sh = Some (skt, R) →
    saddress skt = Some a →
    socket_addresses_coh Sn ip →
    socket_addresses_coh (<[sh:=(skt, m :: R)]> Sn) ip.
  Proof.
    intros HM Hsh Hskt HSn sh' skt' R' sa Hsh' Hskt'.
    destruct (decide (sh = sh')) as [->|].
    - rewrite lookup_insert in Hsh'; simplify_eq.
      eapply HSn; eauto.
    - rewrite lookup_insert_ne in Hsh'; last done.
      eapply HSn; eauto.
  Qed.

  Lemma socket_addresses_coh_receive Sn ip sh skt r m :
    Sn !! sh = Some (skt, r ++ [m]) →
    socket_addresses_coh Sn ip →
    socket_addresses_coh (<[sh:=(skt, r)]> Sn) ip.
  Proof. intros Hsn Hcoh sh' skt' r' sa Hsh' Hskt'. ddeq sh sh'; eauto. Qed.


  Lemma socket_addresses_coh_update_sblock Sn sh skt r b ip:
    Sn !! sh = Some (skt, r) →
    socket_addresses_coh Sn ip →
    socket_addresses_coh (<[sh:=({|
                                    saddress := saddress skt;
                                    sblock := b |}, r)]> Sn) ip.
  Proof.
    intros HSn Hcoh sh' kt' r' a' Hsh' Hskt'.
    ddeq sh sh'; eapply Hcoh; eauto.
  Qed.

  (** socket_unbound_empty_buf_coh *)
  Lemma socket_unbound_empty_buf_coh_alloc_socket Sn sh ip skt:
    saddress skt = None →
    socket_unbound_empty_buf_coh Sn ip →
    socket_unbound_empty_buf_coh (<[sh:=(skt, [])]> Sn) ip.
  Proof.
    intros Hskt HSn sh' skt' R Hsh' Hskt'.
    destruct (decide (sh = sh')) as [->|].
    - rewrite lookup_insert in Hsh'; simplify_eq; done.
    - rewrite lookup_insert_ne in Hsh'; last done.
      eapply HSn; eauto.
  Qed.

  Lemma socket_unbound_empty_buf_coh_socketbind Sn sh skt a:
    saddress skt = None →
    socket_unbound_empty_buf_coh Sn (ip_of_address a) →
    socket_unbound_empty_buf_coh
      (<[sh:=(skt <|saddress := Some a|> , [])]> Sn) (ip_of_address a).
  Proof.
    intros Hskt HSn sh' skt' R Hsh' Hskt'.
    destruct (decide (sh = sh')) as [->|].
    - rewrite lookup_insert in Hsh'; simplify_eq; done.
    - rewrite lookup_insert_ne in Hsh'; last done.
      eapply HSn; eauto.
  Qed.

  Lemma socket_unbound_empty_buf_coh_deliver_message M Sn sh ip skt a R m :
    m ∈ messages_to_receive_at a M →
    Sn !! sh = Some (skt, R) →
    saddress skt = Some a →
    socket_unbound_empty_buf_coh Sn ip →
    socket_unbound_empty_buf_coh (<[sh:=(skt, m :: R)]> Sn) ip.
  Proof.
    intros HM Hsh Hskt HSn sh' skt' R' Hsh' Hskt'.
    destruct (decide (sh = sh')) as [->|].
    - rewrite lookup_insert in Hsh'; simplify_eq; done.
    - rewrite lookup_insert_ne in Hsh'; last done.
      eapply HSn; eauto.
  Qed.

  Lemma socket_unbound_empty_buf_coh_receive Sn ip sh skt r m :
    Sn !! sh = Some (skt, r ++ [m]) →
    socket_unbound_empty_buf_coh Sn ip →
    socket_unbound_empty_buf_coh (<[sh:=(skt, r)]> Sn) ip.
  Proof. intros Hsn Hcoh sh' skt' r' Hsh' Hskt'. ddeq sh sh'; eauto.
         specialize (Hcoh sh' skt' _ Hsn Hskt').
         by apply app_eq_nil in Hcoh as [??].
  Qed.

  Lemma socket_unbound_empty_buf_coh_update_sblock Sn sh skt r b ip:
    Sn !! sh = Some (skt, r) →
    socket_unbound_empty_buf_coh Sn ip →
    socket_unbound_empty_buf_coh (<[sh:=({| saddress := saddress skt;
                                            sblock := b |}, r)]> Sn) ip.
  Proof.
    intros Hsn Hcoh sh' skt' r' Hsh' Hskt'. ddeq sh sh'; eauto.
  Qed.

  (** network_sockets_coh *)
  Lemma network_sockets_coh_alloc_node Sn ps ip :
    Sn !! ip = None →
    network_sockets_coh Sn ps →
    network_sockets_coh (<[ip:=∅]> Sn) ps.
  Proof.
    rewrite /network_sockets_coh.
    intros ? Hcoh ip' ? Hst.
    destruct (decide (ip' = ip)); simplify_eq.
    - apply lookup_insert_rev in Hst. subst. split; done.
    - eapply Hcoh; by rewrite lookup_insert_ne in Hst.
  Qed.

  Lemma network_sockets_coh_init n P : network_sockets_coh {[n:= ∅]} P.
  Proof.
    rewrite /network_sockets_coh.
    intros n' Sn' HSn.
    ddeq n' n;
      [rewrite lookup_insert in HSn
      |rewrite lookup_insert_ne in HSn];
      rewrite /bound_ports_coh
              /socket_handlers_coh
              /socket_messages_coh
              /socket_addresses_coh
              /socket_unbound_empty_buf_coh;
      set_solver.
  Qed.

  Lemma network_sockets_coh_update_sblock σ sh skt r ip Sn b :
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    network_sockets_coh (state_sockets σ) (state_ports_in_use σ) →
    network_sockets_coh
      (<[ip:=<[sh:=({| saddress := saddress skt;
                       sblock := b |}, r)]> Sn]> (state_sockets σ))
      (state_ports_in_use σ).
  Proof.
    rewrite /network_sockets_coh.
    intros ?? Hnets ip' Sn' HSn. ddeq ip' ip; [|eauto].
    destruct (Hnets ip Sn) as (?&?&?&?&?); [done|].
    split; [by eapply bound_ports_coh_update_sblock|].
    split; [by eapply socket_handlers_coh_update_sblock|].
    split; [by eapply socket_messages_coh_update_sblock|].
    split; [by eapply socket_addresses_coh_update_sblock |
            by eapply socket_unbound_empty_buf_coh_update_sblock].
  Qed.

  Lemma network_sockets_coh_alloc_socket S Sn P n sh skt :
    S !! n = Some Sn →
    Sn !! sh = None →
    saddress skt = None →
    network_sockets_coh S P →
    network_sockets_coh (<[n:=<[sh:=(skt, [])]> Sn]> S) P.
  Proof.
    rewrite /network_sockets_coh.
    intros ??? Hnets n' Sn' HSn. ddeq n' n; [|eauto].
    destruct (Hnets n Sn) as (?&?&?&?&?); [done|].
    split; [by apply bound_ports_coh_alloc_socket|].
    split; [by apply socket_handlers_coh_alloc_socket|].
    split; [by apply socket_messages_coh_update_socket|].
    split; [by apply socket_addresses_coh_alloc_socket |
            by apply socket_unbound_empty_buf_coh_alloc_socket].
  Qed.

  Lemma network_sockets_coh_socketbind S P Sn ps sh skt a :
    let ip := ip_of_address a in
    let S' := <[ip:= <[sh:= (skt <| saddress := Some a |>, [])]> Sn]> S in
    let P' := (<[ip:={[port_of_address a]} ∪ ps]> P) in
    S !! ip = Some Sn →
    P !! ip = Some ps →
    Sn !! sh = Some (skt, []) →
    port_of_address a ∉ ps →
    saddress skt = None →
    network_sockets_coh S P  →
    network_sockets_coh S' P'.
  Proof.
    rewrite /network_sockets_coh /=.
    intros ????? Hncoh ip Sn' ?.
    assert
      (∀ sh' skt' r' a',
         Sn !! sh' = Some (skt', r') →
         saddress skt' = Some a' →
         port_of_address a' ≠ port_of_address a ).
    { destruct (Hncoh (ip_of_address a) Sn) as
          (HBpCoh & HshCoh & HmrCoh & HsaCoh);
        [done|].
      intros ** Hp.
      assert (ip_of_address a' = ip_of_address a) as Heq.
      { eapply HsaCoh; eauto. }
      assert (port_of_address a' ∈ ps) as Hin.
      { eapply HBpCoh; eauto. rewrite Heq //. }
      rewrite Hp in Hin. set_solver. }
    ddeq ip (ip_of_address a).
    - destruct (Hncoh (ip_of_address a) Sn) as (?&?&?&?&?); [done|].
      split; [by eapply bound_ports_coh_socketbind|].
      split; [by eapply socket_handlers_coh_socketbind|].
      split; [by eapply socket_messages_coh_update_socket|].
      split; [by eapply socket_addresses_coh_socketbind |].
      apply socket_unbound_empty_buf_coh_socketbind; done.
    - destruct (Hncoh ip Sn') as (HBpCoh & HshCoh & HmrCoh & HsaCoh); [done|].
      split; [|done].
      intros ? skt' a' ???? Hps.
      assert (ip_of_address a' = ip).
      { eapply HsaCoh; eauto. }
      simplify_eq /=. rewrite lookup_insert_ne in Hps; [|done].
      by eapply HBpCoh.
  Qed.

  Lemma network_sockets_coh_receive P S Sn ip sh skt r m :
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r ++ [m]) →
    network_sockets_coh S P →
    network_sockets_coh (<[ip:=<[sh:=(skt, r)]> Sn]> S) P.
  Proof.
    rewrite /network_sockets_coh.
    intros HS HSn Hnet ip' Sn0 HSn0.
    ddeq ip' ip; [|eauto].
    specialize (Hnet ip Sn HS)
      as (Hbcoh & Hshcoh & Hsmcoh & Hsaddrcoh & Hbufcoh).
    split; [by eapply bound_ports_coh_receive|].
    split; [by eapply socket_handlers_coh_receive|].
    split; [by eapply socket_messages_coh_receive|].
    split; [by eapply socket_addresses_coh_receive |].
    by eapply socket_unbound_empty_buf_coh_receive.
  Qed.

  Lemma network_sockets_coh_deliver_message M P S Sn Sn' ip sh skt a r m :
    m ∈ messages_to_receive_at a M →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    Sn' = <[sh:=(skt, m :: r)]> Sn →
    saddress skt = Some a →
    network_sockets_coh S P →
    network_sockets_coh (<[ip:=Sn']> S) P.
  Proof.
    rewrite /network_sockets_coh.
    intros Hm HSn Hsh HSn' Hskt Hnet ip' Sn0 HSn0.
    ddeq ip' ip; [|eauto].
    specialize (Hnet ip Sn HSn)
      as (Hbcoh & Hshcoh & Hsmcoh & Hsaddrcoh & Hbufcoh).
    split; [by eapply bound_ports_coh_deliver_message|].
    split; [by eapply socket_handlers_coh_deliver_message|].
    split; [by eapply socket_messages_coh_deliver_message|].
    split; [by eapply socket_addresses_coh_deliver_message |].
    by eapply socket_unbound_empty_buf_coh_deliver_message.
  Qed.

End state_interpretation.
