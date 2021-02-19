From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
From iris_string_ident Require Import ltac2_string_ident.
From aneris.program_logic Require Export weakestpre adequacy.
From aneris.program_logic Require Import ectx_lifting.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import
     aneris_lang notation network resources.
From aneris.aneris_lang.state_interp Require Import
     state_interp_def.
From aneris.aneris_lang.lib Require Import util.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Σ}.


  (** bound_ports_coh *)
  Lemma bound_ports_coh_alloc_socket Sn P sh skt :
    Sn !! sh = None →
    saddress skt = None →
    bound_ports_coh Sn P →
    bound_ports_coh (<[sh:=(skt, ∅)]> Sn) P.
  Proof.
    intros ??? sh' ???? Hup.
    destruct (decide (sh = sh')) as [Heq|];
      simplify_map_eq.
    - rewrite lookup_insert in Hup. simplify_eq /=.
      intros. simplify_eq /=.
    - rewrite lookup_insert_ne in Hup; eauto.
  Qed.


  Lemma bound_ports_coh_socketbind P Sn ps sh skt a :
    let Sn' := (<[sh:=(skt <| saddress := Some a |>, ∅)]> Sn) in
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
    Sn !! sh = Some (skt, r) →
    bound_ports_coh Sn P →
    bound_ports_coh (<[sh:=(skt, r ∖ {[m]})]> Sn) P.
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
    bound_ports_coh (<[sh:=(skt, R ∪ {[m]})]> Sn) P.
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
    socket_handlers_coh (<[sh:=(s, ∅)]> Sn).
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
    socket_handlers_coh (<[sh:=(skt <| saddress := Some a |>, ∅)]> Sn).
  Proof.
    intros ? Hscoh sh1 sh2 skt1 skt2 ????? Heq.
    ddeq sh1 sh; ddeq sh2 sh; simplify_eq=>//.
    - destruct skt, skt2; simplify_map_eq. set_solver.
    - destruct skt, skt1. simplify_map_eq. set_solver.
    - destruct skt1, skt2. simplify_map_eq. eapply Hscoh; eauto.
  Qed.

 Lemma socket_handlers_coh_receive Sn sh skt r m :
   Sn !! sh = Some (skt, r) →
    socket_handlers_coh Sn →
    socket_handlers_coh (<[sh:=(skt, r ∖ {[m]})]> Sn).
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
   socket_handlers_coh (<[sh:=(skt, R ∪ {[m]})]> Sn).
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

 (** socket_messages_coh *)
 Lemma socket_messages_coh_update_socket Sn sh skt :
   socket_messages_coh Sn →
   socket_messages_coh (<[sh:=(skt, ∅)]> Sn).
 Proof. intros ? sh' **. ddeq sh sh'; [set_solver|]. eauto. Qed.

  Lemma socket_messages_coh_insert_received a sh skt m r Sn :
    Sn !! sh = Some (skt, r) →
    m_destination m = a →
    saddress skt = Some a →
    socket_messages_coh Sn →
    socket_messages_coh (<[sh:=(skt, {[m]} ∪ r)]> Sn).
  Proof.
    intros ??? Hmcoh sh' skt' r' a' Hsh' ?.
    destruct (decide (sh = sh')); simplify_eq; last first.
    { rewrite lookup_insert_ne // in Hsh'. by eapply Hmcoh. }
    rewrite lookup_insert in Hsh'; simplify_eq.
    intros m' [?%elem_of_singleton_1 | HR]%elem_of_union; subst; [done|].
      by eapply Hmcoh.
  Qed.

  Lemma socket_messages_coh_deliver_message M Sn sh skt a R m :
    m ∈ messages_to_receive_at a M →
    Sn !! sh = Some (skt, R) →
    saddress skt = Some a →
    socket_messages_coh Sn →
    socket_messages_coh (<[sh:=(skt, R ∪ {[m]})]> Sn).
  Proof.
    intros HM Hsh Hskt HSn sh' kt' r' a' Hsh' Hskt'.
    destruct (decide (sh = sh')); simplify_eq; last first.
    { rewrite lookup_insert_ne // in Hsh'. by eapply HSn. }
    rewrite lookup_insert in Hsh'; simplify_eq.
    intros m' [HR | ?%elem_of_singleton_1]%elem_of_union; subst.
    - by eapply HSn.
    - apply elem_of_filter in HM as [? ?]; done.
  Qed.

  Lemma socket_messages_coh_receive Sn sh skt r m :
    m ∈ r →
    Sn !! sh = Some (skt, r) →
    socket_messages_coh Sn →
    socket_messages_coh (<[sh:=(skt, r ∖ {[m]})]> Sn).
  Proof.
    intros Hm HSn Hcoh sh' kt' r' a' Hsh' Hskt' m' Hm'.
    ddeq sh sh'; eapply Hcoh; eauto.
    ddeq m m'; set_solver.
  Qed.

  (** socket_addresses_coh *)
  Lemma socket_addresses_coh_alloc_socket Sn sh skt n :
    saddress skt = None →
    socket_addresses_coh Sn n →
    socket_addresses_coh (<[sh:=(skt, ∅)]> Sn) n.
  Proof. intros ? ? sh' **. ddeq sh' sh; eauto. Qed.

  Lemma socket_addresses_coh_socketbind Sn sh skt a :
    saddress skt = None →
    socket_addresses_coh Sn (ip_of_address a) →
    socket_addresses_coh
      (<[sh:=(skt <| saddress := Some a |>, ∅)]> Sn) (ip_of_address a).
  Proof. intros ? ? sh' **; ddeq sh sh'; eauto. Qed.

  Lemma socket_addresses_coh_insert_received sh a skt m R Sn :
    saddress skt = Some a →
    socket_addresses_coh Sn (ip_of_address a) →
    socket_addresses_coh (<[sh:=(skt, R ∪ {[m]})]> Sn) (ip_of_address a).
  Proof. intros ?? sh' **; ddeq sh sh'; eauto. Qed.

  Lemma socket_addresses_coh_deliver_message M Sn sh ip skt a R m :
    m ∈ messages_to_receive_at a M →
    Sn !! sh = Some (skt, R) →
    saddress skt = Some a →
    socket_addresses_coh Sn ip →
    socket_addresses_coh (<[sh:=(skt, R ∪ {[m]})]> Sn) ip.
  Proof.
    intros HM Hsh Hskt HSn sh' skt' R' sa Hsh' Hskt'.
    destruct (decide (sh = sh')) as [->|].
    - rewrite lookup_insert in Hsh'; simplify_eq.
      eapply HSn; eauto.
    - rewrite lookup_insert_ne in Hsh'; last done.
      eapply HSn; eauto.
  Qed.

  Lemma socket_addresses_coh_receive Sn ip sh skt r m :
    Sn !! sh = Some (skt, r) →
    socket_addresses_coh Sn ip →
    socket_addresses_coh (<[sh:=(skt, r ∖ {[m]})]> Sn) ip.
  Proof. intros Hsn Hcoh sh' skt' r' sa Hsh' Hskt'. ddeq sh sh'; eauto. Qed.

  (** socket_unbound_empty_buf_coh *)
  Lemma socket_unbound_empty_buf_coh_alloc_socket Sn sh ip skt:
    saddress skt = None →
    socket_unbound_empty_buf_coh Sn ip →
    socket_unbound_empty_buf_coh (<[sh:=(skt, ∅)]> Sn) ip.
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
      (<[sh:=(skt <|saddress := Some a|> , ∅)]> Sn) (ip_of_address a).
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
    socket_unbound_empty_buf_coh (<[sh:=(skt, R ∪ {[m]})]> Sn) ip.
  Proof.
    intros HM Hsh Hskt HSn sh' skt' R' Hsh' Hskt'.
    destruct (decide (sh = sh')) as [->|].
    - rewrite lookup_insert in Hsh'; simplify_eq; done.
    - rewrite lookup_insert_ne in Hsh'; last done.
      eapply HSn; eauto.
  Qed.

  Lemma socket_unbound_empty_buf_coh_receive Sn ip sh skt r m :
    Sn !! sh = Some (skt, r) →
    socket_unbound_empty_buf_coh Sn ip →
    socket_unbound_empty_buf_coh (<[sh:=(skt, r ∖ {[m]})]> Sn) ip.
  Proof. intros Hsn Hcoh sh' skt' r' Hsh' Hskt'. ddeq sh sh'; eauto.
         specialize (Hcoh sh' skt' r Hsn Hskt'). set_solver.
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

  Lemma network_sockets_coh_alloc_socket S Sn P n sh skt :
    S !! n = Some Sn →
    Sn !! sh = None →
    saddress skt = None →
    network_sockets_coh S P →
    network_sockets_coh (<[n:=<[sh:=(skt, ∅)]> Sn]> S) P.
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
    let S' := <[ip:= <[sh:= (skt <| saddress := Some a |>, ∅)]> Sn]> S in
    let P' := (<[ip:={[port_of_address a]} ∪ ps]> P) in
    S !! ip = Some Sn →
    P !! ip = Some ps →
    Sn !! sh = Some (skt, ∅) →
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
    m ∈ r →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    network_sockets_coh S P →
    network_sockets_coh (<[ip:=<[sh:=(skt, r ∖ {[m]})]> Sn]> S) P.
  Proof.
    rewrite /network_sockets_coh.
    intros Hm HS HSn Hnet ip' Sn0 HSn0.
    ddeq ip' ip; [|eauto].
    specialize (Hnet ip Sn HS)
      as (Hbcoh & Hshcoh & Hsmcoh & Hsaddrcoh & Hbufcoh).
    split; [by eapply bound_ports_coh_receive|].
    split; [by eapply socket_handlers_coh_receive|].
    split; [by eapply socket_messages_coh_receive|].
    split; [by eapply socket_addresses_coh_receive |].
    by apply socket_unbound_empty_buf_coh_receive.
  Qed.

  Lemma network_sockets_coh_deliver_message M P S Sn Sn' ip sh skt a r m :
    m ∈ messages_to_receive_at a M →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    Sn' = <[sh:=(skt, r ∪ {[m]})]> Sn →
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

(*
  Lemma network_sockets_coh_insert_sent S P M Sn sh skt a to m R T :
    let ip := ip_of_address a in
    let msg := mkMessage a to (sprotocol skt) m in
    saddress skt = Some a →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    network_sockets_coh S M P →
    network_sockets_coh (<[ip:=<[sh:=(skt, R, {[msg]} ∪ T)]> Sn]> S) ({[msg]} ∪ M) P.
  Proof.
    intros ip msg Hsa Hsi Hh HnetCoh ip' Sn' Hip'.
    ddeq ip' ip.
    - destruct (HnetCoh ip Sn Hsi) as (HBpCoh & HshCoh & HsmCoh & HsaCoh).
      split.
      { intros sh' skt' **. ddeq sh' sh; eauto using HBpCoh. }
      split.
      { intros sh1 sh2 skt1 skt2 ???? Hsh1 Hsh2 Hskt1 Hsaddr.
        ddeq sh1 sh; ddeq sh2 sh; simplify_eq /=;
          eapply HshCoh; eauto; eapply mk_is_Some; rewrite Hsaddr //. }
      split.
      { intros sh' **; ddeq sh' sh; split; intros;
          edestruct HsmCoh; set_solver. }
      intros sh' **; ddeq sh' sh; eauto.
    - destruct (HnetCoh ip' Sn' Hip') as (HBpCoh & HshCoh & HsmCoh & HsaCoh).
      split; eauto. split; eauto. split; last done.
      intros sh' **. edestruct HsmCoh; eauto.
      split; intros ??; set_solver.
  Qed.

  Lemma network_sockets_coh_not_received a skt sh S Sn P M R T m :
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    m_destination m = a →
    m ∈ M →
    m ∉ R →
    network_sockets_coh S M P →
    ¬ message_received S m.
  Proof.
    intros HS HSn Hskt Hd HM HR Hsock Hr.
    destruct Hr as (Sn' & sh' & skt' & a' & R' & T' & HS' & HSn' & Hs' & Hm).
    destruct (decide (a = a')) as [ | Ha]; simplify_eq.
    - assert (sh = sh') as <-.
      { eapply Hsock; eauto. rewrite Hs' //. }
      by simplify_eq.
    - destruct (Hsock (ip_of_address a') Sn')
        as (?&Hhandlers'&Hmsg'&?); [done|].
      destruct (Hmsg' _ _ _ _ a' HSn') as [HR' ?]; [done|].
      by destruct (HR' _ Hm) as [? ?].
  Qed.

  Lemma network_sockets_coh_insert_received a skt sh S Sn P M R T m :
    let S' := (<[ip_of_address a:=<[sh:=(skt, {[m]} ∪ R, T)]> Sn]> S) in
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    m_destination m = a →
    m ∈ M →
    m ∉ R →
    network_sockets_coh S M P →
    network_sockets_coh S' M P.
  Proof.
    rewrite /network_sockets_coh.
    intros HS HSn ???? Hnet ip' Sn' HSn'.
    destruct (decide (ip_of_address a = ip'));
      simplify_map_eq; [|by eapply Hnet].
    destruct (Hnet _ _ HS) as (?&?&?&?).
    split; [by eapply bound_ports_coh_insert_received|].
    split; [by eapply socket_handlers_coh_insert_received|].
    split; [by eapply socket_messages_coh_insert_received|].
    by eapply socket_addresses_coh_insert_received.
  Qed.

  Lemma network_sockets_messages_coh_insert_received a skt sh S Sn P M R T m :
    let S' := (<[ip_of_address a:=<[sh:=(skt, {[m]} ∪ R, T)]> Sn]> S) in
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    m_destination m = a →
    m ∈ M →
    m ∉ R →
    network_sockets_coh S M P →
    network_messages_coh S M -∗
    network_messages_coh S' M ∗
      ∃ φ : socket_interp Σ, m_destination m ⤇ φ ∗ ▷ φ m.
  Proof.
    iIntros (S' ???????) "Hmcoh".
    rewrite /network_messages_coh big_sepS_delete //.
    iDestruct "Hmcoh" as "[[Hm | %Hr] Hmsgs]";
      [|exfalso; by eapply network_sockets_coh_not_received].
    iFrame.
    assert (message_received S' m) as Hr.
    { by eapply message_received_receive. }
    rewrite (big_sepS_delete _ M m) //. iFrame "%".
    iApply big_sepS_mono; [|done].
    iIntros (??) "[? | %Hr']"; [eauto|].
    iRight. iPureIntro.
    by eapply message_received_insert.
  Qed.
 *)

(*
  (** network_coh **)
  Lemma network_coh_init ip ips P :
    dom (gset ip_address) P = ips →
    (∀ ip, ip ∈ ips → P !! ip = Some ∅) →
    ⊢ network_sockets_coh {[ip:=∅]} ∅ P.
  Proof.
    intros ??. rewrite /network_coh /network_messages_coh.
    iSplit; [|done].
    iPureIntro. rewrite /network_sockets_coh.
    intros ?? [<- <-]%lookup_singleton_Some.
    rewrite /bound_ports_coh /socket_handlers_coh
            /socket_messages_coh /socket_addresses_coh.
    set_solver.
  Qed.

 *)

(*
  Lemma network_coh_sent_valid m sh a skt S Sn M P R T :
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    m ∈ T →
    network_coh S M P -∗ ⌜m ∈ M⌝.
  Proof.
    iIntros (Hs HSn Ha Hm) "(%Hscoh & _)". iPureIntro.
    destruct (Hscoh _ Sn Hs) as (?&?& Hmsgs &?).
    edestruct (Hmsgs sh) as [? HT]; [done..|].
    by apply HT.
  Qed.

  Lemma network_coh_received_valid m sh a skt S Sn M P R T :
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    m ∈ R →
    network_coh S M P -∗ ⌜m ∈ M⌝.
  Proof.
    iIntros (Hs HSn Ha Hm) "(%Hscoh & _)". iPureIntro.
    destruct (Hscoh _ Sn Hs) as (?&?& Hmsgs &?).
    edestruct (Hmsgs sh) as [HR ?]; [done..|].
    by apply HR.
  Qed.

  Lemma network_coh_alloc_node Sn M ps ip :
    Sn !! ip = None →
    network_coh Sn M ps -∗
    network_coh (<[ip:=∅]>Sn) M ps.
  Proof.
    iIntros (Hnone) "[% Hmsg]".
    rewrite /network_coh.
    iSplitR; last first.
    { by iApply network_messages_coh_alloc_node. }
    iPureIntro.
    by apply network_sockets_coh_alloc_node.
  Qed.

  Lemma network_coh_alloc_socket S M P Sn n sh skt :
    S !! n = Some Sn →
    Sn !! sh = None →
    saddress skt = None →
    network_coh S M P -∗
    network_coh (<[n:=<[sh:=(skt, ∅, ∅)]> Sn]> S) M P.
  Proof.
    iIntros (? ? ?) "(% & Hmsg)". iSplitR.
    - iPureIntro. by apply network_sockets_coh_alloc_socket.
    - by iApply network_messages_coh_alloc_socket.
  Qed.

  Lemma network_coh_socketbind S P M Sn ps sh skt a :
    let ip := ip_of_address a in
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, ∅, ∅) →
    P !! ip = Some ps →
    saddress skt = None →
    port_of_address a ∉ ps →
    network_coh S M P -∗
    network_coh
    (<[ip:=<[sh:=(skt <| saddress := Some a |>, ∅, ∅)]> Sn]> S) M
    (<[ip:= {[port_of_address a]} ∪ ps]> P).
  Proof.
    iIntros (??????) "(% & Hmsg)". iSplit.
    - iPureIntro; by apply network_sockets_coh_socketbind.
    - by iDestruct (network_messages_coh_socketbind with "Hmsg") as "Hmsg".
  Qed.

  Lemma network_coh_insert_sent S P M Sn sh skt a to m (φ : socket_interp Σ) R T :
    let ip := ip_of_address a in
    let msg := mkMessage a to (sprotocol skt) m in
    let S' := <[ip := <[sh:=(skt, R, {[msg]} ∪ T)]> Sn]> S in
    let M' := {[msg]} ∪ M in
    saddress skt = Some a →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    to ⤇ φ -∗
    φ msg -∗
    network_coh S M P -∗ network_coh S' M' P.
  Proof.
    iIntros (???????) "Hpred Hr [% Hmsg]". iSplit.
    - iPureIntro. by apply network_sockets_coh_insert_sent.
    - by iApply (network_messages_coh_insert_sent with "Hpred Hr Hmsg").
  Qed.

  Lemma network_coh_receive a sh skt S Sn M P R T m :
    let ip := ip_of_address a in
    let S' := (<[ip:=<[sh:=(skt, {[m]} ∪ R, T)]> Sn]> S) in
    saddress skt = Some a →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    m_destination m = a →
    m ∈ M →
    m ∉ R →
    network_coh S M P -∗ network_coh S' M P ∗ ∃ φ, m_destination m ⤇ φ ∗ ▷ φ m.
  Proof.
    simpl. iIntros (??????) "[%Hsock Hmcoh]".
    rewrite /network_coh.
    iDestruct (network_sockets_messages_coh_insert_received with "Hmcoh")
      as "[Hmcoh Hφ]"; [done..|].
    iFrame. iPureIntro.
    by apply network_sockets_coh_insert_received.
   Qed.*)

End state_interpretation.
