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

Definition messages_history := prod message_soup message_soup.

Definition messages_history_map := gmap socket_address messages_history.


Implicit Types mh : messages_history_map.
Implicit Types rt : messages_history.


(* The set of all received messages *)
Definition messages_received mh := collect (λ _ rt, rt.1) mh.

Lemma elem_of_messages_received mh :
  ∀ m, m ∈ messages_received mh ↔
         ∃ sa rt, mh !! sa = Some rt ∧ m ∈ rt.1.
Proof. by apply elem_of_collect; eauto. Qed.

(* The set of all transmitted messages *)
Definition messages_sent mh := collect (λ _ rt, rt.2) mh.

Lemma elem_of_messages_sent mh :
  ∀ m, m ∈ messages_sent mh ↔
         ∃ sa rt, mh !! sa = Some rt ∧ m ∈ rt.2.
Proof. by apply elem_of_collect; eauto. Qed.


(** Definitions for the message history *)
Definition messages_received_sent mh : messages_history :=
  (messages_received mh, messages_sent mh).

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
    rewrite -Hsa in Hips. by rewrite Hips in Hmh.
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

Lemma messages_received_init ip ports mh :
  history_init ip ports ##ₘ mh →
  messages_received (history_init ip ports ∪ mh) =
  messages_received mh.
Proof.
  intros Hdij.
  rewrite /message_received /messages_received.
  erewrite collect_disjoint_union; last done.
  erewrite history_init_received.
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

 Lemma messages_received_insert  a R T mh :
   messages_received (<[a:=(R, T)]> mh) = R ∪ messages_received (delete a mh).
 Proof.
   rewrite /messages_received.
   apply collect_insert.
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


(* The messages in the logical map mh, that tracks
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
    destruct (decide (a' = (m_sender m))) as [->|Hneq].
    - by rewrite lookup_delete in Ha'.
    - rewrite lookup_delete_ne in Ha'; last done.
    destruct (Hmcoh a' R' T' Ha') as (_ & HT').
    specialize (HT' m Ht).
    done.
  Qed.
