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

 Lemma buffers_subseteq S ip Sn skt r r' sh :
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    r ⊆ r' →
    buffers S ⊆ buffers (<[ip:=<[sh:=(skt, r')]> Sn]> S).
  Proof.
    intros.
    intros m Hm.
    apply elem_of_collect in Hm as (ip1 & Sip1 & HSip1 & Hm).
    ddeq ip ip1.
    - apply elem_of_collect in Hm as (h1 & (s1, r1) & Hhsr1 & Hm).
      apply elem_of_collect.
      ddeq sh h1.
      + exists ip1, (<[h1:=(skt, r')]> Sn). rewrite lookup_insert; eauto.
        split; first done.
        apply elem_of_collect.
        exists h1, (skt,r'). split; last set_solver.
        rewrite lookup_insert. eauto.
      + exists ip1, (<[sh:=(skt, r')]> Sn). rewrite lookup_insert.
         split; first done.
         apply elem_of_collect.
         exists h1, (s1,r1).
         rewrite lookup_insert_ne; eauto.
    - apply elem_of_collect in Hm as (h1 & (s1, r1) & Hhsr1 & Hm).
      apply elem_of_collect.
      exists ip1, Sip1. rewrite lookup_insert_ne; eauto.
      split; first done.
      apply elem_of_collect.
      set_solver.
  Qed.

  (* Lemma tes (r r' : message_soup) : *)
  (*   r' ⊆ r → *)
  (*   r ∖ (r ∖ r') = r'.   *)
  (* Proof. rewrite set_eq_subseteq; split; set_solver. Qed. *)

  Lemma buffers_retreive S ip Sn skt r r' sh :
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    r' ⊆ r →
    r' = buffers S ∖ buffers (<[ip:=<[sh:=(skt, r ∖ r')]> Sn]> S).
  Proof. Admitted.

  Lemma buffers_subseteq_new_ip S ip :
    S !! ip = None →
    buffers S ⊆ buffers (<[ip:=∅]> S).
  Proof.
    intros Hnone.
    rewrite /buffers.
    rewrite insert_union_singleton_l.
    rewrite collect_disjoint_union.
    set_solver.
    by apply map_disjoint_singleton_l_2.
  Qed.

  Lemma buffers_subseteq_new_socket S Sn ip sh f t p:
    S !! ip = Some Sn →
    Sn !! sh = None →
    buffers S ⊆ buffers (<[ip:=<[sh:=(mkSocket f t p None true, ∅)]> Sn]> S).
  Proof.
    intros Hip Hnone.
    rewrite /buffers.
    intros m Hm.
    apply elem_of_collect in Hm as (ip1 & Sip1 & HSip1 & Hm).
    ddeq ip ip1.
    - apply elem_of_collect in Hm as (h1 & (s1, r1) & Hhsr1 & Hm).
      apply elem_of_collect.
      ddeq sh h1.
      + exists ip1, (<[sh:=(mkSocket f t p None true, ∅)]> Sn).
        rewrite lookup_insert; eauto.
        split; first done.
        apply elem_of_collect.
        exists h1. eexists. split; last set_solver.
          by rewrite lookup_insert_ne.
    - apply elem_of_collect in Hm as (h1 & (s1, r1) & Hhsr1 & Hm).
      apply elem_of_collect.
      exists ip1, Sip1. rewrite lookup_insert_ne; eauto.
      split; first done.
      apply elem_of_collect.
      set_solver.
  Qed.

  Lemma buffers_subseteq_update_socket S Sn ip sh sa skt r:
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    buffers S ⊆ buffers (<[ip:=<[sh:=(skt<| saddress := sa |>, r)]> Sn]> S).
  Proof.
    intros.
    intros m Hm.
    apply elem_of_collect in Hm as (ip1 & Sip1 & HSip1 & Hm).
    ddeq ip ip1.
    - apply elem_of_collect in Hm as (h1 & (s1, r1) & Hhsr1 & Hm).
      apply elem_of_collect.
      ddeq sh h1.
      + exists ip1, (<[h1:=(skt<| saddress := sa |>, r)]> Sn).
        rewrite lookup_insert; eauto.
        split; first done.
        apply elem_of_collect.
        exists h1, (skt<| saddress := sa |>, r). split; last set_solver.
        rewrite lookup_insert. eauto.
      + exists ip1, (<[sh:=(skt<| saddress := sa |>, r)]> Sn).
        rewrite lookup_insert.
        split. f_equal.
        apply elem_of_collect.
        exists h1, (s1,r1).
        rewrite lookup_insert_ne; eauto.
    - apply elem_of_collect in Hm as (h1 & (s1, r1) & Hhsr1 & Hm).
      apply elem_of_collect.
      exists ip1, Sip1. rewrite lookup_insert_ne; eauto.
      split; first done.
      apply elem_of_collect.
      set_solver.
  Qed.

  Lemma message_history_evolution_new_socket S Sn ip M mh sh f t p:
    S !! ip = Some Sn →
    Sn !! sh = None →
    mh = message_history_evolution
         M M S (<[ip:=<[sh:=(mkSocket f t p None true, ∅)]> Sn]> S) mh.
 Proof.
    intros ??. rewrite /message_history_evolution.
    destruct mh as (R,T).
    rewrite !difference_diag_L !left_id_L. f_equal.
    rewrite subseteq_empty_difference_L; first set_solver.
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
    rewrite subseteq_empty_difference_L; first set_solver.
    rewrite /buffers. simplify_eq /=.
    by eapply buffers_subseteq_update_socket.
 Qed.

  Lemma message_history_evolution_deliver_message ip Sn sh skt r r' S M rt :
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    r ⊆ r' →
    rt = message_history_evolution
           M M S (<[ip:=<[sh:=(skt, r')]> Sn]> S) rt.
  Proof.
    intros ???.
    rewrite /message_history_evolution.
    destruct rt as (R, T).
    simplify_eq /=.
    rewrite !difference_diag_L left_id_L. f_equal.
    rewrite subseteq_empty_difference_L; first set_solver.
    by eapply buffers_subseteq.
  Qed.

  Lemma message_history_evolution_drop_message S M M' rt :
    M' ⊆ M →
    rt = message_history_evolution M M' S S rt.
  Proof.
    intros ?.
    rewrite /message_history_evolution.
    destruct rt as (R, T).
    rewrite !difference_diag_L left_id_L. f_equal.
    rewrite subseteq_empty_difference_L; eauto.
    set_solver.
  Qed.

  Lemma message_history_evolution_receive ip S Sn M sh skt r R mh m:
    m ∈ r →
    R ⊆ mh.1 →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    ({[ m ]} ∪ R ∪ mh.1, mh.2) =
    message_history_evolution
      M M S  (<[ip :=<[sh:=(skt, r ∖ {[m]})]> Sn]> S) mh.
  Proof.
    intros Hmr HR HS HSn.
    rewrite /message_history_evolution.
    rewrite !difference_diag_L !left_id_L.
    f_equal. assert ({[m]} ∪ mh.1 =  {[m]} ∪ R ∪ mh.1) as Heq by set_solver.
    rewrite -Heq. f_equal.
    eapply buffers_retreive; set_solver; eauto.
  Qed.

  Lemma message_history_evolution_send_message S M msg mh :
    M ⊆ mh.2 →
    (mh.1, {[msg]} ∪ mh.2) = message_history_evolution M ({[msg]} ∪ M) S S mh.
  Proof.
    intro Hms. rewrite /message_history_evolution.
    destruct mh as (R,T).
    rewrite !difference_diag_L !left_id_L.
    f_equal. simpl.
    destruct (decide (msg ∈ M)) as [Hin | Hnotin].
    - rewrite difference_union_distr_l_L.
      rewrite subseteq_empty_difference_L; last set_solver.
      rewrite !difference_diag_L !left_id_L. set_solver.
    - set_solver.
  Qed.

  Lemma message_history_evolution_send_duplicate_message S M msg mh :
    msg ∈ mh.2 →
    (mh.1, mh.2) = message_history_evolution M ({[msg]} ∪ M) S S mh.
  Proof.
    intro Hms. rewrite /message_history_evolution.
    destruct mh as (R,T).
    rewrite !difference_diag_L !left_id_L.
    f_equal. simpl.
    destruct (decide (msg ∈ M)) as [Hin | Hnotin].
    - rewrite difference_union_distr_l_L.
      rewrite subseteq_empty_difference_L; last set_solver.
      rewrite !difference_diag_L !left_id_L. set_solver.
    - set_solver.
  Qed.

  Lemma message_history_evolution_new_ip S ip M mh :
    S !! ip = None →
    mh = message_history_evolution M M S (<[ip := ∅]>S) mh.
  Proof.
    intros ?. rewrite /message_history_evolution.
    destruct mh as (r,t).
    rewrite !difference_diag_L !left_id_L. f_equal.
    rewrite subseteq_empty_difference_L; first set_solver.
    rewrite /buffers. simplify_eq /=. by eapply buffers_subseteq_new_ip.
  Qed.

   Lemma valid_state_evolution_id σ  (δ : Mdl) mh :
    mh = message_history_evolution
           (state_ms σ) (state_ms σ) (state_sockets σ)
           (state_sockets σ) mh
    ∧ user_model_evolution δ δ.
    Proof. split; last by left; eauto.
           rewrite /message_history_evolution.
           rewrite !difference_diag_L !left_id_L.
             by destruct mh.
    Qed.




(* Lemma get_buffer_some r sh skt Sn S a :
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

  Lemma get_buffer_none S a  :
    S !! ip_of_address a = None →
    get_buffer S a = None.
  Proof.
    intros Hip.
    destruct (get_buffer S a) eqn:Heq1; last done.
    apply get_buffer_inv in Heq1 as (sh0 & skt0 & Sn0 & HS0 & HSn0 & Hskt0).
    naive_solver.
  Qed.

   Lemma get_buffer_none_2 S a  :
    S !! ip_of_address a = Some ∅ →
    get_buffer S a = None.
  Proof.
    intros Hip.
    destruct (get_buffer S a) eqn:Heq1; last done.
    apply get_buffer_inv in Heq1 as (sh0 & skt0 & Sn0 & HS0 & HSn0 & Hskt0).
    naive_solver.
  Qed.

   Lemma get_buffer_none_3 S a  :
    S !! ip_of_address a = None →
    get_buffer (<[ip_of_address a := ∅]> S) a = None.
  Proof.
    intros Hip.
    eapply get_buffer_none_2.
    rewrite lookup_insert. naive_solver.
  Qed.

  Lemma get_buffer_none_inv S a  :
     get_buffer S a = None →
     S !! ip_of_address a = Some ∅ ∨
     (∃ Sn, S !! ip_of_address a = Some Sn ∧
            (forall sh skt r, Sn !! sh = Some (skt, r) →
                         saddress skt ≠ Some a)) ∨
     S !! ip_of_address a = None.
   Proof.
     intros Hbuf. rewrite /get_buffer in Hbuf.
     apply bind_None in Hbuf as [|Hbuf]; first by naive_solver.
     destruct Hbuf as (Sn & HSn & Hfind).
     apply fmap_None in Hfind.
     destruct (decide (Sn = ∅)) as [->|Hneq].
     - by left.
     - right. left.
       exists Sn. split; first done.
       intros.
       apply find_none with (x:=(sh,(skt,r))) in Hfind.
       + simpl in Hfind. by case_bool_decide.
       + apply elem_of_list_In.
         by apply elem_of_map_to_list.
   Qed.

  Lemma get_buffer_new_ip S a ip :
    (∀ ip Sn, S !! ip = Some Sn → socket_handlers_coh Sn) →
    S !! ip = None →
    get_buffer S a = get_buffer (<[ip:=∅]> S) a.
  Proof.
    intros Hcoh Hs.
    ddeq (ip_of_address a) ip.
    - erewrite get_buffer_none, get_buffer_none_3; eauto.
    - destruct (get_buffer S a) eqn:Heq1;
        destruct (get_buffer (<[ip:=∅]> S) a) eqn:Heq2; last done.
      + apply get_buffer_inv in Heq1 as (sh0 & skt0 & Sn0 & HS0 & HSn0 & Hskt0).
        apply get_buffer_inv in Heq2 as (sh1 & skt1 & Sn1 & HS1 & HSn1 & Hskt1).
        rewrite lookup_insert_ne in HS1; last done.
        rewrite HS0 in HS1. simplify_eq /=.
        assert (sh0 = sh1) as ->.
        { eapply (Hcoh (ip_of_address a) Sn1 HS0); eauto.
            by rewrite Hskt0 Hskt1. }
        naive_solver.
      + apply get_buffer_none_inv in Heq2.
        rewrite lookup_insert_ne in Heq2; last done.
        apply get_buffer_inv in Heq1 as (sh0 & skt0 & Sn0 & HS0 & HSn0 & Hskt0).
        naive_solver.
      + apply get_buffer_none_inv in Heq1.
        apply get_buffer_inv in Heq2 as (sh0 & skt0 & Sn0 & HS0 & HSn0 & Hskt0).
        rewrite lookup_insert_ne in HS0; last done.
        naive_solver.
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

  Lemma  sent_received_at_evolution_new_ip
         S ip M (mh : messages_history_map) a rt:
    (∀ ip Sn, S !! ip = Some Sn → socket_handlers_coh Sn) →
    S !! ip = None →
    mh !! a = Some rt →
    rt = sent_received_at_evolution M M S (<[ip:=∅]> S) a rt.
  Proof.
    intros ???.
    rewrite /sent_received_at_evolution.
    match goal with |-  _ = default _ ?x => destruct x eqn:Heq end; last done.
    destruct (get_buffer S a) eqn:Hbeq; last done.
    destruct (get_buffer (<[ip := ∅]>S) a) eqn:Hbeq'; last done.
    rewrite -get_buffer_new_ip in Hbeq'; last done.
    simpl in Heq. rewrite !difference_diag_L in Heq.
    simplify_eq /=.
    rewrite /messages_sent_from filter_empty_L  !difference_diag_L !right_id_L.
    simplify_eq. by destruct rt. done.
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

  Lemma message_history_evolution_new_ip S ip M mh :
    (∀ ip Sn, S !! ip = Some Sn → socket_handlers_coh Sn) →
    S !! ip = None →
    mh = message_history_evolution M M S (<[ip := ∅]>S) mh.
  Proof.
    intros ??. rewrite-{1}(map_imap_Some mh) /message_history_evolution.
    apply map_imap_ext. intros a'.
    destruct (mh !! a') eqn:Hmh; rewrite Hmh; last done; simpl.
    do 2 f_equal. by eapply sent_received_at_evolution_new_ip.
  Qed.


  Lemma valid_state_evolution_id σ (δ : Mdl) mh :
    mh = message_history_evolution
           (state_ms σ) (state_ms σ) (state_sockets σ)
           (state_sockets σ) mh
    ∧ user_model_evolution δ δ.
  Proof. split; last by left; eauto. eapply message_history_evolution_id. Qed.

  *)

End Aneris_AS.
