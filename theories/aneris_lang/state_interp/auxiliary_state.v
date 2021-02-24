From stdpp Require Import fin_maps gmap option.
From aneris.prelude Require Import quantifiers.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From iris_string_ident Require Import ltac2_string_ident.
From aneris.program_logic Require Export weakestpre adequacy.
From aneris.program_logic Require Import ectx_lifting.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Export aneris_lang notation network resources.
From aneris.aneris_lang.lib Require Import util.
From aneris.aneris_lang.state_interp Require Import
     state_interp_def
     state_interp_network_sockets_coh
     state_interp_socket_interp_coh
     state_interp_messages_history_coh.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Section Aneris_AS.
  Context `{aG : !anerisG Mdl Σ}.

  Lemma get_buffer_some r sh skt Sn S a :
    socket_handlers_coh Sn →
    S !! (ip_of_address a) = Some Sn →
    Sn !! sh = Some (skt, r) →
    saddress skt = Some a →
    get_buffer S a = Some r.
  Proof.
    intros Hskcoh HS HSn Hskt. rewrite /get_buffer HS /=.
    destruct (find _ _) as [[sh' [skt' r']]|] eqn:Hf; simpl in *; last first.
    { apply elem_of_map_to_list, elem_of_list_In in HSn.
      eapply find_none in Hf; last done.
      rewrite bool_decide_eq_true_2 in Hf; done. }
    apply find_some in Hf as [Hf1 Hf2%bool_decide_eq_true].
    apply elem_of_list_In, elem_of_map_to_list' in Hf1.
    simpl in *. assert (sh' = sh) as ->.
    { apply (Hskcoh sh' sh skt' skt r' r); eauto. rewrite Hskt Hf2; done. }
    rewrite Hf1 in HSn; simplify_eq; done.
  Qed.

  Lemma get_buffer_inv r S a :
    get_buffer S a = Some r →
    ∃ sh skt Sn,
      S !! (ip_of_address a) = Some Sn ∧
      Sn !! sh = Some (skt, r) ∧
      saddress skt = Some a.
  Proof.
    intros Hbuf. rewrite /get_buffer in Hbuf.
    apply bind_Some in Hbuf as (Sn & HSn & Hfind).
    apply fmap_Some in Hfind as ((h0,(s0,r0)) & Hfind & ->).
    apply find_some in Hfind as (Hin & Hbl%bool_decide_eq_true).
    apply elem_of_list_In, elem_of_map_to_list' in Hin. simpl in *. eauto 9.
  Qed.


  Lemma get_buffer_deliver_message S M Sn sh skt a r m :
    let S' := (<[ip_of_address a := (<[sh:=(skt, r ∪ {[m]})]> Sn) ]> S) in
    m ∈ messages_to_receive_at a M →
    S !! (ip_of_address a) = Some Sn →
    Sn !! sh = Some (skt, r) →
    saddress skt = Some a →
    socket_handlers_coh Sn  →
    get_buffer S' a = Some (r ∪ {[m]}).
  Proof.
    simpl. intros ?????.
    eapply (get_buffer_some _ sh) ;
      [ eapply socket_handlers_coh_deliver_message ; eauto | eauto.. ].
    - by rewrite lookup_insert.
    - by rewrite lookup_insert.
  Qed.

   Lemma sent_received_at_evolution_id S M a rt :
    rt = sent_received_at_evolution M M S S a rt.
  Proof.
    rewrite /sent_received_at_evolution.
    match goal with |-  _ = default _ ?x => destruct x eqn:Heq end; last done.
    destruct (get_buffer S a) eqn:Hbeq; last done.
    simpl in Heq. rewrite !difference_diag_L in Heq.
    rewrite /messages_sent_from filter_empty_L !right_id_L in Heq.
    simplify_eq. by destruct rt.
  Qed.

  Lemma sent_received_at_evolution_drop_message
        m M S a RT (mh : messages_history_map):
    m ∈ M →
    mh !! a = Some RT →
    RT = sent_received_at_evolution M (M ∖ {[m]}) S S a RT.
  Proof.
    intros Hm Hmha. rewrite /sent_received_at_evolution.
    match goal with |-  _ = default _ ?x => destruct x eqn:Heq end; last done.
    destruct (get_buffer S a) eqn:Hbeq; last done.
    simpl in Heq. rewrite difference_diag_L right_id_L in Heq.
    assert (M ∖ {[m]} ∖ M = ∅) as Hest by set_solver. rewrite Hest in Heq.
    rewrite /messages_sent_from filter_empty_L right_id_L in Heq.
    rewrite -Heq. simpl. by destruct RT.
  Qed.

  Lemma sent_received_at_evolution_deliver_message ip Sn sh a skt r m S M RT :
    m ∈ messages_to_receive_at a M →
    socket_handlers_coh Sn →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    ip = ip_of_address a →
    saddress skt = Some a →
    RT = sent_received_at_evolution
           M M S (<[ip:=<[sh:=(skt, r ∪ {[m]})]> Sn]> S) a RT.
  Proof.
    intros ??????.
    rewrite /sent_received_at_evolution.
    match goal with |-  _ = default _ ?x => destruct x eqn:Heq end; last done.
    destruct (get_buffer S a) eqn:Hbeq; last done.
    simpl in Heq. rewrite difference_diag_L in Heq.
    rewrite /messages_sent_from filter_empty_L right_id_L in Heq.
    simplify_eq. erewrite get_buffer_deliver_message in Heq; eauto.
    simpl in *.
    erewrite get_buffer_some in Hbeq; eauto.
    simplify_eq.
    assert (m0 ∖ (m0 ∪ {[m]}) = ∅) as -> by set_solver.
    rewrite right_id_L. intuition.
  Qed.

  Lemma sent_received_at_evolution_ne
        ip a a' sh skt (mh : messages_history_map) p Sn M S r:
    (∀ ip Sn, S !! ip = Some Sn → socket_handlers_coh Sn) →
    mh !! a' = Some p →
    saddress skt = Some a →
    S !! ip = Some Sn →
    a' ≠ a →
    p = sent_received_at_evolution M M S (<[ip:=<[sh:=(skt, r)]> Sn]> S) a' p.
  Proof.
    intros Hcoh???HSn?.
    rewrite /sent_received_at_evolution.
    match goal with |-  _ = default _ ?x => destruct x eqn:Heq end; last done.
    destruct (get_buffer S a') eqn:Hbeq; last done.
    simpl in Heq. rewrite difference_diag_L in Heq.
    rewrite /messages_sent_from filter_empty_L right_id_L in Heq.
    destruct
      (get_buffer (<[ip:=<[sh:=(skt, r)]> Sn]> S) a') eqn:Heq2; last done.
    simpl in *.
    apply get_buffer_inv in Hbeq as (sh0 & skt0 & Sn0 & HS0 & HSn0 & Hskt0).
    apply get_buffer_inv in Heq2 as (sh1 & skt1 & Sn1 & HS1 & HSn1 & Hskt1).
    simplify_eq /=.
    ddeq ip (ip_of_address a').
    - ddeq sh sh1.
      + assert (sh0 = sh1) as ->.
        { eapply (Hcoh (ip_of_address a') Sn HSn sh0 sh1 skt0 skt1); eauto.
            by rewrite Hskt0 Hskt1. }
        simplify_map_eq /=. rewrite difference_diag_L right_id_L.
          by destruct p.
    - assert (sh0 = sh1) as ->.
      { eapply (Hcoh (ip_of_address a') Sn0 HS0 sh0 sh1 skt0 skt1); eauto.
          by rewrite Hskt0 Hskt1. }
      simplify_map_eq /=. rewrite difference_diag_L right_id_L.
        by destruct p.
  Qed.

  Lemma message_history_evolution_deliver_message ip Sn sh a skt r m S M mh :
    m ∈ messages_to_receive_at a M →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    ip = ip_of_address a →
    saddress skt = Some a →
    (∀ ip Sn, S !! ip = Some Sn → socket_handlers_coh Sn) →
    mh =
    message_history_evolution M M S (<[ip:=<[sh:=(skt, r ∪ {[m]})]> Sn]> S) mh.
  Proof.
    intros ??????Hcoh.
    rewrite-{1}(map_imap_Some mh).
    rewrite /message_history_evolution.
    apply map_imap_ext.
    intros a'.
    destruct (mh !! a') eqn:Hmh; rewrite Hmh; last done; simpl.
    do 2 f_equal.
    destruct (decide (a' = a)) as [->|Hneq].
    - specialize (Hcoh ip Sn).
      eapply sent_received_at_evolution_deliver_message; eauto.
    - rewrite /sent_received_at_evolution.
        by eapply sent_received_at_evolution_ne.
  Qed.

  Lemma message_history_evolution_drop_message m S M mh :
    m ∈ M →
    mh = message_history_evolution M (M ∖ {[m]}) S S mh.
  Proof.
    intros ?. rewrite-{1}(map_imap_Some mh).
    rewrite /message_history_evolution. apply map_imap_ext.
    intros a'. destruct (mh !! a') eqn:Hmh; rewrite Hmh; last done; simpl.
    do 2 f_equal. by eapply sent_received_at_evolution_drop_message.
  Qed.

  Lemma message_history_evolution_id S M mh :
    mh = message_history_evolution M M S S mh.
  Proof.
    rewrite-{1}(map_imap_Some mh) /message_history_evolution. apply map_imap_ext.
    intros a'. destruct (mh !! a') eqn:Hmh; rewrite Hmh; last done; simpl.
    do 2 f_equal. by eapply sent_received_at_evolution_id.
  Qed.


  Lemma valid_state_evolution_id σ (δ : Mdl) mh :
    mh = message_history_evolution
           (state_ms σ) (state_ms σ) (state_sockets σ)
           (state_sockets σ) mh
    ∧ user_model_evolution δ δ.
  Proof. split; last by left; eauto. eapply message_history_evolution_id. Qed.


End Aneris_AS.
