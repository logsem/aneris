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

Lemma gset_to_gmap_singleton (v: message_soup * message_soup)
      (a : socket_address) : gset_to_gmap v {[ a ]} = {[a := v]}.
Proof.
  assert ({[a]} = {[a]} ∪ (∅: gset socket_address)) as -> by by set_solver.
    by rewrite (gset_to_gmap_union_singleton v a ∅) gset_to_gmap_empty.
Qed.

Lemma messages_received_init B :
  messages_received (gset_to_gmap (∅, ∅) B) = ∅.
Proof.
  rewrite /messages_received.
  apply collect_empty_f.
  intros ? [].
  rewrite lookup_gset_to_gmap_Some.
  by intros [? [=]].
Qed.

Lemma messages_sent_init B :
  messages_sent (gset_to_gmap (∅, ∅) B) = ∅.
Proof.
  rewrite /messages_sent.
  apply collect_empty_f.
  intros ? [].
  rewrite lookup_gset_to_gmap_Some.
  by intros [? [=]].
Qed.

Lemma messages_received_sent_init B :
  messages_received_sent (gset_to_gmap (∅, ∅) B) = (∅, ∅).
Proof.
  rewrite /messages_received_sent. f_equal.
  - apply messages_received_init.
  - apply messages_sent_init.
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

(* The messages in the logical map mh, that tracks received and transmitted
   messages, have coherent addresses. *)
Definition messages_addresses_coh mh :=
  ∀ a R T, mh !! a = Some (R, T) →
    (∀ m, m ∈ R → m_destination m = a) ∧ (∀ m, m ∈ T → m_sender m = a).

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
