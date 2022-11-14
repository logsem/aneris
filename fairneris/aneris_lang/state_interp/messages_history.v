From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From aneris.prelude Require Import collect.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Export aneris_lang network resources.
From aneris.algebra Require Import disj_gsets.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Definition messages_history := prod message_soup message_soup.

Definition messages_history_map := gmap socket_address_group messages_history.

Implicit Types mhm : messages_history_map.
Implicit Types rt : messages_history.

(* The set of all received messages *)
Definition messages_received mhm := collect (λ _ rt, rt.1) mhm.

Lemma elem_of_messages_received mhm :
  ∀ m, m ∈ messages_received mhm ↔
       ∃ sa rt, mhm !! sa = Some rt ∧ m ∈ rt.1.
Proof. by apply elem_of_collect; eauto. Qed.

(* The set of all transmitted messages *)
Definition messages_sent mhm := collect (λ _ rt, rt.2) mhm.

Lemma elem_of_messages_sent mhm :
  ∀ m, m ∈ messages_sent mhm ↔
       ∃ sa rt, mhm !! sa = Some rt ∧ m ∈ rt.2.
Proof. by apply elem_of_collect; eauto. Qed.

(** Definitions for the message history *)
Definition messages_received_sent mhm : messages_history :=
  (messages_received mhm, messages_sent mhm).

(* [m] has been received *)
Definition message_received m mhm := m ∈ (messages_received mhm).

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

Lemma messages_sent_insert a R T mhm :
  messages_sent (<[a:=(R, T)]> mhm) = T ∪ messages_sent (delete a mhm).
Proof.
  rewrite /messages_sent.
  apply collect_insert.
Qed.

Lemma message_received_insert a msg R T mhm :
  message_received msg (<[a:=(R, T)]> mhm) ↔
  msg ∈ R ∨ message_received msg (delete a mhm).
Proof.
  rewrite /message_received /messages_received.
  rewrite collect_insert //= elem_of_union //.
Qed.

Lemma messages_received_insert  a R T mhm :
  messages_received (<[a:=(R, T)]> mhm) = R ∪ messages_received (delete a mhm).
Proof.
  rewrite /messages_received.
  apply collect_insert.
Qed.

Lemma messages_sent_split a R T mhm :
  mhm !! a = Some (R, T) →
  messages_sent mhm =
  T ∪ messages_sent (delete a mhm).
Proof.
  intros.
  assert (mhm = <[a := (R,T)]>mhm) as Heq by by rewrite insert_id.
  rewrite {1} Heq.
  apply collect_insert.
Qed.

(* The messages in the logical map mhm, that tracks received and transmitted
   messages, have coherent addresses. *)
Definition messages_addresses_coh mhm :=
  all_disjoint (dom mhm) ∧
  set_Forall (λ x, x ≠ ∅) (dom mhm) ∧
  ∀ sag R T, mhm !! sag = Some (R, T) →
             (∀ m, m ∈ R → m_destination m ∈ sag) ∧
             (∀ m, m ∈ T → m_sender m ∈ sag).

Definition messages_received_from_sent_coh mhm :=
  messages_received mhm ⊆ messages_sent mhm.

Definition messages_received_from_sent_coh_aux mhm :=
  ∀ rt sag m,
  m_destination m ∈ sag →
  mhm !! sag = Some rt →
  m ∈ rt.1 →
  ∃ rt' sag', m_sender m ∈ sag' →
              mhm !! sag' = Some rt' ∧ m ∈ rt'.2.

Lemma messages_received_from_sent_corrolary_coh mhm :
  messages_addresses_coh mhm →
  messages_received_from_sent_coh mhm →
  messages_received_from_sent_coh_aux mhm.
Proof.
  intros (Hdisj & Hne & Hacoh) Hrcoh.
  intros rt sag m Hsag Hrt Hm.
  assert (m ∈ (messages_received mhm)) as Hmr.
  { by apply elem_of_collect; eauto. }
  apply Hrcoh, elem_of_collect in Hmr as (sa & rt' & Hrt' & Hmt).
  assert (mhm !! sa = Some (rt'.1, rt'.2)) as Hgas by by destruct rt'.
  specialize (Hacoh sa rt'.1  rt'.2 Hgas) as (Hc1 & Hc2).
  specialize (Hc2 m Hmt). set_solver.
Qed.

Lemma messages_sent_dijsoint sag R T mhm :
  mhm !! sag = Some (R, T) →
  messages_addresses_coh mhm →
  T ## messages_sent (delete sag mhm).
Proof.
  intros Hsag (Hdisj & Hne & Hmcoh).
  apply elem_of_disjoint.
  intros m HmT Hms.
  apply elem_of_collect in Hms as (sag' & (R',T') & Hsag' & Ht).
  simplify_map_eq.
  destruct (Hmcoh sag R T Hsag) as (HR & HT).
  specialize (HT m HmT).
  assert (sag ≠ sag') as Hineq.
  { destruct (decide (sag = sag')); [ | done ].
    subst. by rewrite lookup_delete in Hsag'. }
  rewrite lookup_delete_ne in Hsag'; last by set_solver.
  assert (sag ## sag') as Hdisj'.
  { assert (sag ∈ (dom mhm)) as Hin.
    { apply elem_of_dom. eexists _. apply Hsag. }
    assert (sag' ∈ (dom mhm)) as Hin'.
    { apply elem_of_dom. eexists _. apply Hsag'. }
    destruct (Hdisj sag sag' Hin Hin') as [H | H]; done. }
  destruct (Hmcoh sag' R' T' Hsag') as (_ & HT').
  specialize (HT' m Ht).
  set_solver.
Qed.

Lemma messages_received_in mh sag m R T :
  messages_addresses_coh mh →
  mh !! sag = Some (R,T) →
  m_destination m ∈ sag →
  message_received m mh →
  m ∈ R.
Proof.
  intros [Hdisj [Hne Hmhcoh]] Hmh Hin Hrecv.
  pose proof (Hmhcoh sag R T Hmh) as [Hdest Hsrc].
  apply elem_of_messages_received in Hrecv.
  destruct Hrecv as (sa & rt & Hlookup & Hin').
  destruct rt as [R' T'].
  pose proof (Hmhcoh sa R' T' Hlookup) as [Hdest' _].
  specialize (Hdest' m Hin').
  assert (sa = sag) as ->.
  { eapply elem_of_all_disjoint_eq; eauto.
    apply elem_of_dom. eexists _. set_solver.
    apply elem_of_dom. eexists _. set_solver. }
  simpl in *.
  rewrite Hlookup in Hmh.
  set_solver.
Qed.

Lemma message_received_delete m mh sag1 sag2 :
  messages_addresses_coh mh →
  m_destination m ∈ sag1 →
  sag1 ∈ dom mh →
  sag2 ∈ dom mh →
  sag1 ≠ sag2 →
  message_received m mh →
  message_received m (delete sag2 mh).
Proof.
  rewrite /message_received.
  rewrite !elem_of_messages_received.
  intros (Hdisj & Hne & Hcoh) Hdest Hsag1 Hsag2 Hrecv
         [sag [[R T] [Hlookup Hin]]].
  assert (sag = sag1) as ->.
  { eapply elem_of_all_disjoint_eq; eauto.
    apply elem_of_dom. eexists _. set_solver.
    eapply Hcoh. eauto. eauto. }
  eexists sag1, (R,T).
  rewrite lookup_delete_ne; last done.
  auto.
Qed.
