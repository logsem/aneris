From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
From iris_string_ident Require Import ltac2_string_ident.
From aneris.program_logic Require Export weakestpre adequacy.
From aneris.program_logic Require Import ectx_lifting.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Export
     aneris_lang notation network resources
     state_interp_def.
From aneris.aneris_lang.lib Require Import util.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Σ}.

  (** messages_sent *)
  Lemma messages_sent_empty ip : messages_sent {[ip:=∅]} = ∅.
  Proof.
    rewrite /messages_sent.
    rewrite /collect.
    rewrite -insert_empty.
    rewrite -insert_delete.
    rewrite /messages_sent map_fold_insert_L; [set_solver | | set_solver].
    intros j j' z z' m Hneq Hj Hj'.
    assert (z = ∅) as ->.
    { rewrite insert_delete insert_empty in Hj Hj'.
      ddeq j ip.
      - rewrite lookup_insert in Hj. set_solver.
      - rewrite lookup_insert_ne in Hj; set_solver. }
    assert (z' = ∅) as ->.
     { rewrite insert_delete insert_empty in Hj Hj'.
      ddeq j' ip.
      - rewrite lookup_insert in Hj'. set_solver.
      - rewrite lookup_insert_ne in Hj'; set_solver. }
    done.
  Qed.

  Lemma messages_resource_coh_init ip : ⊢ messages_resource_coh {[ip := ∅]}.
  Proof.
    iIntros. by rewrite /messages_resource_coh messages_sent_empty.
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
