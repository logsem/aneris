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

  Lemma messages_resource_coh_init ip ports :
    ⊢ messages_resource_coh (history_init ip ports).
  Proof.
    iIntros. by rewrite /messages_resource_coh history_init_sent.
  Qed.

  Lemma messages_resource_coh_alloc_node mh ip ports :
    history_init ip ports ##ₘ mh →
    messages_resource_coh mh -∗
    messages_resource_coh (history_init ip ports ∪ mh).
  Proof.
    rewrite /messages_resource_coh /=.
    iIntros (?) "Hsent".
    rewrite messages_sent_init; last done.
    rewrite big_sepS_mono; first done.
    iIntros (??) "[? | %]"; [by iLeft|].
    iRight. iPureIntro.
      by apply message_received_init.
  Qed.

  Lemma message_received_insert_sent_message a msg msg' R T mh :
    mh !! a = Some (R, T) →
    messages_addresses_coh mh →
    T ## messages_sent (delete a mh) →
    msg' ∈ T ∨ msg' ∈ messages_sent (delete a mh) →
    message_received msg' mh →
    message_received msg' (<[a:=(R, {[msg]} ∪ T)]> (delete a mh)).
  Proof.
    intros Hsrc  Hmcoh Hdisj Hmsg' Hrd.
    rewrite (insert_delete mh a).
    eapply message_received_insert; eauto.
    apply elem_of_collect in Hrd as (a' & (R',T') & Hdlt & Hrd).
    ddeq a' a.
    simplify_map_eq.
    right. apply elem_of_collect.
    exists a', (R',T'). by simplify_map_eq.
  Qed.

  Lemma messages_resource_coh_send mh a R T msg ϕ :
    msg ∉ T →
    mh !! a = Some (R, T) →
    m_sender msg = a →
    messages_addresses_coh mh →
    m_destination msg ⤇ ϕ -∗
    messages_resource_coh mh -∗
    ϕ msg -∗
    messages_resource_coh (<[a:=(R, {[msg]} ∪ T)]> mh).
  Proof.
    rewrite /messages_resource_coh /=.
    iIntros (Hmt Hsrc Hmh Hmcoh) "#Hϕ Hcoh Hm".
    rewrite -(insert_delete mh a).
    rewrite messages_sent_insert.
    rewrite {1} (messages_sent_split a R T); last done.
    assert (T ## messages_sent (delete a mh)) as Hdisj.
    { by eapply messages_sent_dijsoint. }
    rewrite !big_sepS_union; last done.
    - rewrite big_sepS_singleton.
      iDestruct "Hcoh" as "(HcohT & Hcoh)".
      iSplitL "Hm HcohT".
      + iSplitL "Hm".
        * iLeft. eauto.
        * rewrite big_sepS_mono; first done.
           iIntros (msg' Hmsg') "[Htt | %Hrd]"; first by iLeft.
           iRight. iPureIntro.
           eapply message_received_insert_sent_message; eauto.
      + eauto with iFrame.
        rewrite delete_idemp.
        rewrite big_sepS_mono; first done.
        iIntros (msg' Hmsg') "[Htt | %Hrd]"; first by iLeft.
        iRight. iPureIntro.
        eapply message_received_insert_sent_message; eauto.
    - set_solver.
    - rewrite delete_idemp.
      apply disjoint_union_l.
      split; last done.
      apply elem_of_disjoint.
      intros m HmT Hms.
      erewrite elem_of_singleton in HmT.
      subst.
      apply elem_of_collect in Hms as (a' & (R',T') & Ha' & Ht).
      simplify_map_eq.
      ddeq a' (m_sender msg).
      erewrite lookup_delete_ne in Ha'; last done.
      destruct (Hmcoh a' R' T' Ha') as (_ & HT).
      specialize (HT msg Ht).
      done.
  Qed.

  Lemma messages_resource_coh_receive a b R T R' T' m mh :
    m_destination m = a →
    m_sender m = b →
    mh !! a = Some (R, T) →
    mh !! b = Some (R',T') →
    m ∉ R  →
    m ∈ T' →
    messages_addresses_coh mh →
    messages_resource_coh mh -∗
    messages_resource_coh (<[a:=({[m]} ∪ R, T)]> mh) ∗
    ∃ φ, m_destination m ⤇ φ ∗ ▷ φ m.
  Proof.
    iIntros (Hmd Hms Hmha Hmhb HmR HmT' Hmacoh).
    iIntros "Hrcoh". rewrite /messages_resource_coh.
    assert (messages_sent mh = messages_sent (<[a:=(R, T)]>mh)) as Heq.
    { apply insert_id in Hmha as Heq. by rewrite {1} Heq. }
    rewrite {1} Heq.
    assert ((messages_sent (<[a:=(R, T)]> mh) ∖ {[m]}) =
            (messages_sent (<[a:=({[m]} ∪ R, T)]> mh) ∖ {[m]})) as Hdelm.
    { by rewrite !messages_sent_insert. }
    assert (m ∈ messages_sent (<[a:=(R, T)]> mh)) as Hsent.
    { rewrite -Heq. apply elem_of_messages_sent. set_solver. }
    assert (m ∈ messages_sent (<[a:=({[m]} ∪ R, T)]> mh)) as Hsent2.
    { rewrite messages_sent_insert. by rewrite messages_sent_insert in Hsent. }
    assert (message_received m (<[a:=({[m]} ∪ R, T)]> mh) ) as Hrcd.
    { rewrite message_received_insert. left. set_solver. }
    assert (m ∉ messages_received mh) as Hnotrcd.
    { intro Habs. apply elem_of_messages_received in Habs
        as (sa & (R0, T0) & Hmh & Hm). simplify_map_eq.
      specialize (Hmacoh sa R0 T0) as (H1 & H2); first done.
      specialize (H1 m Hm). set_solver. }
    iPoseProof (big_opS_delete
                  (fun m0 => ((∃ Φ, m_destination m0 ⤇ Φ ∗ ▷ Φ m0)
                           ∨ ⌜message_received m0 mh⌝))%I
                  (messages_sent (<[a:=(R, T)]> mh)) m) as "Hdel"; first done.
    iPoseProof ("Hdel" with "Hrcoh") as "([Hr|%Hr] & Hrcoh)"; last done.
    iPoseProof (big_opS_delete
                  (fun m0 => ((∃ Φ, m_destination m0 ⤇ Φ ∗ ▷ Φ m0)
                     ∨ ⌜message_received m0 (<[a:=({[m]} ∪ R, T)]> mh)⌝))%I
                  (messages_sent (<[a:=({[m]} ∪ R, T)]> mh)) m) as "Hdel2";
      first done. iFrame. rewrite {2} Hdelm. iApply "Hdel2". iSplitR; eauto.
    iApply (big_sepS_mono with "Hrcoh"). iIntros (msg Hmsg) "[Hm|%Hm]".
    - iLeft. iFrame.
    - iRight. iPureIntro. apply insert_id in Hmha. rewrite -Hmha in Hm.
      erewrite message_received_insert in Hm. rewrite message_received_insert.
      destruct Hm as [?|Hm]; set_solver.
  Qed.



  (** message_received *)
  (* TODO: FIXME *)
  (*
  Lemma message_received_alloc_socket S m Sn ip sh s:
    S !! ip = Some Sn →
    Sn !! sh = None →
    message_received S m →
    message_received (<[ip:=<[sh:=(s, ∅, ∅)]> Sn]> S) m.
  Proof.
    rewrite /message_received.
    intros HSn HhNone (Sn' & sh' & s' & a & R & T & HS' & HSn' & Ha & Hm).
    destruct (decide (ip = ip_of_address a)); simplify_map_eq.
    - eexists  (<[sh:=(s, ∅, ∅)]> Sn), _, _, a, _, _.
      rewrite lookup_insert. repeat split; try done.
      rewrite lookup_insert_ne //.
    - do 6 eexists. rewrite lookup_insert_ne //.
  Qed.

  Lemma message_received_socketbind S m Sn sh skt a:
    let ip := ip_of_address a in
    let S' := (<[ip:=<[sh:=(skt <| saddress := Some a |>, ∅, ∅)]> Sn]> S) in
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, ∅, ∅) →
    message_received S m →
    message_received S' m.
  Proof.
    rewrite /message_received.
    intros HSn HhSome (? & sh' &?& a' &?&?&HS&?&?&?).
    destruct (decide (ip_of_address a = ip_of_address a')) as [Heq|];
      simplify_map_eq.
    - rewrite -Heq in HS.
      destruct (decide (sh = sh')); simplify_map_eq; [done|].
      eexists (<[sh:=(skt<| saddress := Some a |>, ∅, ∅)]> Sn), _, _, a',  _, _.
      rewrite Heq lookup_insert lookup_insert_ne //.
    - do 6 eexists. rewrite lookup_insert_ne //.
  Qed.

  Lemma message_received_receive a skt sh S Sn R T m :
    let S' := (<[ip_of_address a:=<[sh:=(skt, {[m]} ∪ R, T)]> Sn]> S) in
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    message_received S' m.
  Proof.
    intros ????. rewrite /message_received /S'.
    exists (<[sh:=(skt, {[m]} ∪ R, T)]> Sn), sh, skt, a, ({[m]} ∪ R), T.
    rewrite !lookup_insert //. repeat split; eauto. set_solver.
  Qed.

  Lemma message_received_insert a skt sh S Sn R T m m' :
    let S' := (<[ip_of_address a:=<[sh:=(skt, {[m']} ∪ R, T)]> Sn]> S) in
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    message_received S m →
    message_received S' m.
  Proof.
    intros S' HS HSn ? Hr.
    destruct (decide (m = m')); simplify_eq.
    { by apply message_received_receive. }
    destruct Hr as (Sn' & sh' & skt' & a' & R' & T' & HS' & HSn' & Ha' & Hm).
    rewrite /S' /message_received.
    destruct (decide (ip_of_address a = ip_of_address a')) as [Heq | ?].
    - exists (<[sh:=(skt, {[m']} ∪ R, T)]> Sn).
      rewrite -Heq in HS'.
      assert (Sn = Sn') as <- by set_solver.
      destruct (decide (sh' = sh)); simplify_eq.
      + exists sh, skt, a, ({[m']} ∪ R), T.
        rewrite !lookup_insert. repeat split; eauto with set_solver.
      + exists sh', skt', a', R', T'.
        rewrite Heq ?lookup_insert ?lookup_insert_ne //.
    - do 6 eexists. rewrite lookup_insert_ne //.
   Qed.
   *)

   (* TODO: FIXME *)
  (*
  (** network_messages_coh *)
  Lemma network_messages_coh_alloc_node Sn M ip :
    Sn !! ip = None →
    network_messages_coh Sn M -∗
    network_messages_coh (<[ip:=∅]> Sn) M.
  Proof.
    iIntros (Hnone) "H".
    iApply big_sepS_mono; last done.
    iIntros (??) "[? | %Hr]"; first by iLeft.
    destruct Hr as (a & h & Sn' & s & R & T &?&?&?&?).
    iRight. iPureIntro. exists a, h, Sn', s, R, T.
    simplify_map_eq. set_solver.
  Qed.

  Lemma network_messages_coh_alloc_socket S Sn M n h sh :
    S !! n = Some Sn →
    Sn !! h = None →
    network_messages_coh S M -∗
    network_messages_coh (<[n:=<[h:=(sh, ∅, ∅)]>Sn]> S) M.
  Proof.
    iIntros (??) "Hsent". rewrite /network_messages_coh.
    rewrite big_sepS_mono; first done.
    iIntros (??) "[Htt | %]"; [by iLeft|].
    iRight. iPureIntro. by apply message_received_alloc_socket.
  Qed.

  Lemma network_messages_coh_socketbind S M Sn sh skt a :
    let ip := ip_of_address a in
    let S' := (<[ip:=<[sh:=(skt <| saddress := Some a |>, ∅, ∅)]> Sn]> S) in
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, ∅, ∅) →
    saddress skt = None →
    network_messages_coh S M -∗
    network_messages_coh S' M.
  Proof.
    rewrite /network_messages_coh /=.
    iIntros (???) "Hsent".
    rewrite big_sepS_mono; first done.
    iIntros (??) "[? | %]"; [by iLeft|].
    iRight. iPureIntro. by apply message_received_socketbind.
  Qed.

  Lemma network_messages_coh_insert_sent S M Sn sh skt a to m R T φ P :
    let ip := ip_of_address a in
    let msg := mkMessage a to (sprotocol skt) m in
    let S' := <[ip := <[sh:=(skt, R, {[msg]} ∪ T)]> Sn]> S in
    let M' := {[msg]} ∪ M in
    saddress skt = Some a →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    network_sockets_coh S M P →
    to ⤇ φ -∗
    φ msg -∗
    network_messages_coh S M -∗ network_messages_coh S' M'.
  Proof.
    iIntros (ip msg ?? Hsa Hh Hsi HnetCoh) "Hsi Hmsg Hsent".
    rewrite /network_messages_coh /S'.
    destruct (decide (msg ∈ M)).
    - assert (M = M') as <- by set_solver.
      iApply (big_sepS_mono with "Hsent").
      iIntros (msg' Hmsg') "[Htt | Hrd]"; first by iLeft.
      iDestruct "Hrd" as %Hrd. iRight; iPureIntro.
      rewrite /message_received.
      destruct Hrd as (Sa'&sh'&skt'&a'&R'&T'&Hsi'&Hs'&Hsa'&HinR').
      destruct (decide (ip = ip_of_address a')) as [Heq | Heq]; simplify_map_eq.
      + eexists (<[sh:=(skt, R, {[msg]} ∪ T)]> Sn),sh',skt',a'.
        destruct Heq.
        destruct (decide (sh = sh')); do 2 eexists;
          simplify_map_eq; [done|].
        rewrite lookup_insert_ne //.
      + do 6 eexists. rewrite lookup_insert_ne //.
    - rewrite (big_sepS_union _ _ M ) // /=; last by set_solver.
      iSplitL "Hmsg Hsi". rewrite big_sepS_singleton. iLeft. eauto.
      iApply (big_sepS_mono with "Hsent").
      iIntros (msg' Hmsg') "[Htt | Hrd]"; first by iLeft.
      iDestruct "Hrd" as %Hrd. iRight; iPureIntro.
      rewrite /message_received.
      destruct Hrd as (Sa'&sh'&skt'&a'&R'&T'&Hsi'&Hs'&Hsa'&HinR').
      destruct (decide (ip = ip_of_address a')) as [Heq | Heq]; simplify_map_eq.
      + eexists (<[sh:=(skt, R, {[msg]} ∪ T)]> Sn),sh',skt',a'.
        destruct Heq. rewrite lookup_insert.
        destruct (decide (sh = sh')); do 2 eexists;
          simplify_map_eq; [done|].
        rewrite lookup_insert_ne //.
      + do 6 eexists. rewrite lookup_insert_ne //.
  Qed.
*)

End state_interpretation.
