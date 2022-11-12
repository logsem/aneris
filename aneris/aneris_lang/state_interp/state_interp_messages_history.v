From RecordUpdate Require Import RecordSet.
From stdpp Require Import fin_maps gmap option gmultiset.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From trillium.program_logic Require Export traces.
From aneris.prelude Require Import collect gmultiset.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Export aneris_lang network resources.
From aneris.aneris_lang.state_interp Require Import
     state_interp_def
     state_interp_network_sockets_coh
     state_interp_socket_interp_coh
     state_interp_messages_history_coh.

Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

(* TODO: move to stdpp? *)
Lemma elem_of_list_to_set_disj `{EqDecision A, Countable A} (x : A) l:
  x ∈ l -> x ∈ (list_to_set_disj l : gmultiset _).
Proof.
  induction l; first set_solver.
  rewrite list_to_set_disj_cons.
  intros [-> | Hin]%elem_of_cons; multiset_solver.
Qed.

Lemma subseteq_of_buffers S Sn ip skt sh r m:
  S !! ip = Some Sn →
  Sn !! sh = Some (skt, r) →
  m ∈ r →
  m ∈ buffers S.
Proof.
  intros Hsip HSn Hm.
  apply elem_of_multi_collect.
  exists ip, Sn. split; first done.
  apply elem_of_multi_collect.
  eexists _,_. split=>//=. by apply elem_of_list_to_set_disj.
Qed.

Lemma buffers_subseteq S ip Sn skt r sh m:
  S !! ip = Some Sn →
  Sn !! sh = Some (skt, r) →
  buffers S ⊆ buffers (<[ip:=<[sh:=(skt, m :: r)]> Sn]> S).
Proof.
  intros HSn Hsh Hincl.
  apply multi_collect_subseteq.
  intros ip' Sn' HSn'.
  destruct (decide (ip = ip')) as [->|Hneq].
  - eexists. rewrite lookup_insert. split; first done.
    rewrite HSn' in HSn. injection HSn. intros ->.
    apply multi_collect_subseteq. intros sh' [??] Hsh'.
    destruct (decide (sh = sh')) as [<-|Hneq].
    + eexists. rewrite lookup_insert. split; first done. simpl.
      rewrite Hsh in Hsh'. simplify_eq. multiset_solver.
    + eexists. rewrite lookup_insert_ne //.
  - eexists. rewrite lookup_insert_ne //.
Qed.

Lemma set_diff_distr (X Y Z : message_soup) :
  X ## Z →
  Y ## Z →
  (X ∪ Z) ∖ (Y ∪ Z) = X ∖ Y.
Proof.
  intros Hxz Hyz.
  set_solver.
Qed.


Lemma buffers_subseteq_new_ip S ip :
  S !! ip = None →
  buffers S ⊆ buffers (<[ip:=∅]> S).
Proof.
  intros Hnone.
  rewrite /buffers.
  rewrite insert_union_singleton_l.
  rewrite multi_collect_disjoint_union.
  - multiset_solver.
  - by apply map_disjoint_singleton_l_2.
Qed.

(* TODO: deduplicate all the subseteq lemmas in this file. *)
Lemma buffers_subseteq_new_socket S Sn ip sh f t p:
  S !! ip = Some Sn →
  Sn !! sh = None →
  buffers S ⊆ buffers (<[ip:=<[sh:=(mkSocket f t p None true, [])]> Sn]> S).
Proof.
  intros HSn Hsh.
  apply multi_collect_subseteq.
  intros ip' Sn' HSn'.
  destruct (decide (ip = ip')) as [->|Hneq].
  - eexists. rewrite lookup_insert. split; first done.
    rewrite HSn' in HSn. injection HSn. intros ->.
    apply multi_collect_subseteq. intros sh' [??] Hsh'.
    destruct (decide (sh = sh')) as [<-|Hneq].
    + eexists. rewrite lookup_insert. split; first done. simpl.
      rewrite Hsh in Hsh'. by simplify_eq.
    + eexists. rewrite lookup_insert_ne //.
  - eexists. rewrite lookup_insert_ne //.
Qed.

Lemma buffers_subseteq_update_socket S Sn ip sh sa skt r:
  S !! ip = Some Sn →
  Sn !! sh = Some (skt, r) →
  buffers S ⊆ buffers (<[ip:=<[sh:=(skt<| saddress := sa |>, r)]> Sn]> S).
Proof.
  intros HSn Hsh.
  apply multi_collect_subseteq.
  intros ip' Sn' HSn'.
  destruct (decide (ip = ip')) as [->|Hneq].
  - eexists. rewrite lookup_insert. split; first done.
    rewrite HSn' in HSn. injection HSn. intros ->.
    apply multi_collect_subseteq. intros sh' [??] Hsh'.
    destruct (decide (sh = sh')) as [<-|Hneq].
    + eexists. rewrite lookup_insert. split; first done. simpl.
      rewrite Hsh in Hsh'. by simplify_eq.
    + eexists. rewrite lookup_insert_ne //.
  - eexists. rewrite lookup_insert_ne //.
Qed.

Lemma buffers_subseteq_update_socket_sblock S Sn ip sh skt r b:
  S !! ip = Some Sn →
  Sn !! sh = Some (skt, r) →
  buffers S ⊆ buffers (<[ip:=<[sh:=(skt<| sblock := b |>, r)]> Sn]> S).
Proof.
  intros HSn Hsh.
  apply multi_collect_subseteq.
  intros ip' Sn' HSn'.
  destruct (decide (ip = ip')) as [->|Hneq].
  - eexists. rewrite lookup_insert. split; first done.
    rewrite HSn' in HSn. injection HSn. intros ->.
    apply multi_collect_subseteq. intros sh' [??] Hsh'.
    destruct (decide (sh = sh')) as [<-|Hneq].
    + eexists. rewrite lookup_insert. split; first done. simpl.
      rewrite Hsh in Hsh'. by simplify_eq.
    + eexists. rewrite lookup_insert_ne //.
  - eexists. rewrite lookup_insert_ne //.
Qed.

Lemma message_history_evolution_update_sblock S Sn ip M mh sh skt r  b:
  S !! ip = Some Sn →
  Sn !! sh = Some (skt, r) →
  mh = message_history_evolution
         M M S (<[ip:=<[sh:=(skt<| sblock := b |>, r)]> Sn]> S) mh.
Proof.
  intros ??. rewrite /message_history_evolution.
  destruct mh as (R,T).
  rewrite difference_diag_L !left_id_L. f_equal.
  rewrite gmultiset_empty_difference; first set_solver.
  rewrite /buffers. simplify_eq /=.
  by eapply buffers_subseteq_update_socket_sblock.
Qed.

Lemma message_history_evolution_new_socket S Sn ip M mh sh f t p:
  S !! ip = Some Sn →
  Sn !! sh = None →
  mh = message_history_evolution
         M M S (<[ip:=<[sh:=(mkSocket f t p None true, [])]> Sn]> S) mh.
Proof.
  intros ??. rewrite /message_history_evolution.
  destruct mh as (R,T).
  rewrite !difference_diag_L !left_id_L. f_equal.
  rewrite gmultiset_empty_difference; first set_solver.
  rewrite /buffers. simplify_eq /=.
  by eapply buffers_subseteq_new_socket.
Qed.

Lemma message_history_evolution_socketbind S Sn ip M mh sh skt r sa:
  S !! ip = Some Sn →
  Sn !! sh = Some (skt, r) →
  mh = message_history_evolution
         M M S (<[ip:=<[sh:=(skt<| saddress := sa |>, r)]> Sn]> S) mh.
Proof.
  intros ??. rewrite /message_history_evolution.
  destruct mh as (R,T).
  rewrite !difference_diag_L !left_id_L. f_equal.
  rewrite gmultiset_empty_difference; first set_solver.
  rewrite /buffers. simplify_eq /=.
  by eapply buffers_subseteq_update_socket.
Qed.

Lemma message_history_evolution_deliver_message ip Sn sh skt r m S M rt :
  S !! ip = Some Sn →
  Sn !! sh = Some (skt, r) →
  rt = message_history_evolution
         M (M ∖ {[+ m +]}) S (<[ip:=<[sh:=(skt, m::r)]> Sn]> S) rt.
Proof.
  intros ??.
  rewrite /message_history_evolution.
  destruct rt as (R, T).
  assert (gset_of_gmultiset (M ∖ {[+ m +]}) ∖ gset_of_gmultiset M = ∅) as ->.
  { rewrite subseteq_empty_difference_L; [done|].
    intros x Hin%elem_of_gset_of_gmultiset.
    apply elem_of_gset_of_gmultiset.
    destruct (decide (x = m)) as [->|Hneq].
    - rewrite multiplicity_difference multiplicity_singleton in Hin. lia.
    - rewrite multiplicity_difference multiplicity_singleton_ne in Hin; [|done].
      lia. }
  f_equal; [|by set_solver].
  rewrite gmultiset_empty_difference; first set_solver.
  by eapply buffers_subseteq.
Qed.

Lemma message_history_evolution_duplicate_message S M M' rt :
  M' ⊆ M → rt = message_history_evolution M (M ⊎ M') S S rt.
Proof.
  intros ?.
  rewrite /message_history_evolution.
  destruct rt as (R, T).
  rewrite !gmultiset_difference_diag.
  assert (dom (D := message_soup) (∅ : gmultiset _) = ∅) as Hempty by multiset_solver.
  rewrite Hempty. f_equal; [multiset_solver|].
  rewrite gset_of_gmultiset_disj_union_subseteq; [|done].
  rewrite difference_diag_L. set_solver.
Qed.

Lemma message_history_evolution_drop_message S M M' rt :
  M' ⊆ M →
  rt = message_history_evolution M M' S S rt.
Proof.
  intros ?.
  rewrite /message_history_evolution.
  destruct rt as (R, T).
  rewrite !gmultiset_difference_diag.
  assert (dom (D := message_soup) (∅ : gmultiset _) = ∅) as Hempty by multiset_solver.
  rewrite Hempty. f_equal; first multiset_solver.
  rewrite subseteq_empty_difference_L; [|by apply gset_of_gmultiset_subseteq_mono].
  set_solver.
Qed.

(* TODO: add to stdpp *)
Section more_lemmas.
  Context `{Countable A}.
  Implicit Types x y : A.
  Implicit Types X Y Z : gmultiset A.

  Lemma gmultiset_difference_disj_union X Y Z :
    X ∖ Y = (X ⊎ Z) ∖ (Y ⊎ Z).
  Proof.
    multiset_solver.
  Qed.
End more_lemmas.

Lemma message_history_evolution_receive ip S Sn M sh skt r R mh m:
  (∀ ip Sn,
     S !! ip = Some Sn →
     socket_handlers_coh Sn ∧
     socket_addresses_coh Sn ip ∧
     socket_messages_coh Sn ∧
     socket_unbound_empty_buf_coh Sn ip) →
  R ⊆ mh.1 →
  S !! ip = Some Sn →
  Sn !! sh = Some (skt, r ++ [m]) →
  ({[ m ]} ∪ R ∪ mh.1, mh.2) =
  message_history_evolution
    M M S (<[ip :=<[sh:=(skt, r)]> Sn]> S) mh.
Proof.
  intros Hcoh HR HS HSn.
  rewrite /message_history_evolution.
  rewrite !difference_diag_L !left_id_L. f_equal.
  assert ({[m]} ∪ mh.1 =  {[m]} ∪ R ∪ mh.1) as Heq by set_solver.
  rewrite -Heq. f_equal.
  rewrite /buffers /multi_collect.
  rewrite -insert_delete_insert.
  rewrite map_fold_insert; last first.
  { apply lookup_delete. }
  { intros. multiset_solver. }
  rewrite -(insert_delete S ip Sn) //.
  rewrite map_fold_insert; last first.
  { apply lookup_delete. }
  { intros. multiset_solver. }
  rewrite delete_insert; last apply lookup_delete.
  rewrite -gmultiset_difference_disj_union.
  rewrite -insert_delete_insert.
  rewrite map_fold_insert; last first.
  { apply lookup_delete. }
  { intros. multiset_solver. }
  rewrite -(insert_delete Sn sh (skt, r ++ [m])) //.
  rewrite map_fold_insert; last first.
  { apply lookup_delete. }
  { intros. multiset_solver. }
  rewrite delete_insert; last apply lookup_delete.
  rewrite -gmultiset_difference_disj_union /=.
  rewrite list_to_set_disj_app /=.

  match goal with
    [|- _ = dom ?x ] => assert (x = {[+ m +]}) as H; last by rewrite H; multiset_solver
  end.
  multiset_solver.
Qed.

Lemma message_history_evolution_send_message S M msg mh :
  gset_of_gmultiset M ⊆ mh.2 →
  (mh.1, {[msg]} ∪ mh.2) = message_history_evolution M ({[+ msg +]} ⊎ M) S S mh.
Proof.
  intro Hms. rewrite /message_history_evolution.
  destruct mh as (R,T).
  rewrite !gmultiset_difference_diag.
  assert (dom (D := message_soup) (∅ : gmultiset _) = ∅) as Hempty by multiset_solver.
  rewrite Hempty. f_equal; first multiset_solver.
  destruct (decide (msg ∈ T)) as [Hin|Hnin]=> /=.
  - assert ({[msg]} ∪ T = T) as -> by set_solver.
    rewrite gset_of_gmultiset_disj_union
            difference_union_distr_l_L
            difference_diag_L.
    set_solver.
  - rewrite gset_of_gmultiset_disj_union
            difference_union_distr_l_L.
    set_solver.
Qed.

Lemma message_history_evolution_send_duplicate_message S M msg mh :
  msg ∈ mh.2 →
  (mh.1, mh.2) = message_history_evolution M ({[+ msg +]} ⊎ M) S S mh.
Proof.
  intro Hms. rewrite /message_history_evolution.
  destruct mh as (R,T).
  rewrite !gmultiset_difference_diag.
  assert (dom (D := message_soup) (∅ : gmultiset _) = ∅) as Hempty by multiset_solver.
  rewrite Hempty. f_equal; first multiset_solver.
  f_equal.
  rewrite gset_of_gmultiset_disj_union
          difference_union_distr_l_L
          difference_diag_L.
  set_solver.
Qed.

Lemma message_history_evolution_new_ip S ip M mh :
  S !! ip = None →
  mh = message_history_evolution M M S (<[ip := ∅]>S) mh.
Proof.
  intros ?. rewrite /message_history_evolution.
  destruct mh as (r,t).
  rewrite difference_diag_L !left_id_L. f_equal.
  rewrite gmultiset_empty_difference; first set_solver.
  rewrite /buffers. simplify_eq /=. by eapply buffers_subseteq_new_ip.
Qed.

Lemma message_history_evolution_id σ mh :
  mh = message_history_evolution
         (state_ms σ) (state_ms σ) (state_sockets σ)
         (state_sockets σ) mh.
Proof.
  rewrite /message_history_evolution !gmultiset_difference_diag.
  destruct mh. f_equal; set_solver.
Qed.

Lemma trace_messages_history_includes_last ex msg :
  msg ∈ state_ms (trace_last ex).2 → msg ∈ (trace_messages_history ex).2.
Proof.
  revert msg; induction ex as [c|ex IHex c]; intros msg.
  { rewrite elem_of_gset_of_gmultiset elem_of_multiplicity; done. }
  simpl; intros Hmsg.
  destruct (decide (msg ∈ state_ms (trace_last ex).2)) as [Hin|Hnin].
  - apply elem_of_union; right; auto.
  - apply elem_of_union; left.
    apply elem_of_difference. rewrite !elem_of_gset_of_gmultiset. set_solver.
Qed.
