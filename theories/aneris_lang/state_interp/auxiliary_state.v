From stdpp Require Import fin_maps gmap option.
From aneris.prelude Require Import quantifiers.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
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


  Lemma subseteq_of_buffers S Sn ip skt sh r m:
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    m ∈ r →
    m ∈ buffers S.
  Proof.
    intros Hsip HSn Hm.
    apply elem_of_collect.
    exists ip, Sn. split; first done.
    apply elem_of_collect.
    eauto.
  Qed.

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

  Lemma set_diff_distr (X Y Z : message_soup) :
    X ## Z →
    Y ## Z →
    (X ∪ Z) ∖ (Y ∪ Z) = X ∖ Y.
  Proof.
    intros Hxz Hyz.
    set_solver.
  Qed.

  Lemma buffers_retreive S ip Sn skt r r' sh :
    (∀ ip Sn,
        S !! ip = Some Sn →
        socket_handlers_coh Sn ∧
        socket_addresses_coh Sn ip ∧
        socket_messages_coh Sn ∧
        socket_unbound_empty_buf_coh Sn ip) →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    r' ⊆ r →
    r' = buffers S ∖ buffers (<[ip:=<[sh:=(skt, r ∖ r')]> Sn]> S).
  Proof.
    intros Hcoh Hip HSn Hsub. apply insert_id in Hip as Heq1.
    apply insert_id in HSn as Heq2. rewrite -Heq2 in Heq1. rewrite -{1}Heq1.
    rewrite /buffers. rewrite !collect_insert //=.
    assert
      (r ## collect
         (λ (_ : socket_handle)
            (sr : socket * gset message), sr.2) (delete sh Sn)) as Hdisj1.
    { apply elem_of_disjoint. intros m Hmr Hmc.
      apply elem_of_collect in Hmc as (sh1 & (skt1, r1) & Hsh1 & Hm1).
      ddeq sh sh1. assert (is_Some (saddress skt)) as (s & HsktS).
      { destruct (saddress skt) eqn:Hskt; first by naive_solver.
        assert (r = ∅); last set_solver.
        destruct (Hcoh ip Sn Hip) as (Hhcoh & Hacoh & Hmcoh & Hrcoh).
        apply (Hrcoh sh skt r HSn); eauto. }
      assert (is_Some (saddress skt1)) as (s1 & HsktS1).
      { destruct (saddress skt1) eqn:Hskt; first by naive_solver.
        assert (r1 = ∅); last set_solver.
        destruct (Hcoh ip Sn Hip) as (Hhcoh & Hacoh & Hmcoh & Hrcoh).
        apply (Hrcoh sh1 skt1 r1); eauto.
        rewrite -Hsh1. symmetry. by eapply lookup_delete_ne. }
      assert (sh = sh1); last done.
      destruct (Hcoh ip Sn Hip) as (Hhcoh & Hacoh & Hmcoh & Hrcoh).
      destruct (saddress skt) eqn:Hskt;
        destruct (saddress skt1) eqn:Hskt1; [| simplify_eq /=; eauto ..].
      eapply (Hhcoh sh sh1 skt skt1 r r1); eauto.
      rewrite -Hsh1. symmetry. by eapply lookup_delete_ne.
      transitivity (Some (m_destination m)).
      rewrite Hskt. f_equal. symmetry. by eapply (Hmcoh sh skt r s0 HSn).
      rewrite Hskt1. f_equal. eapply (Hmcoh sh1 skt1 r1 s2); last done.
      rewrite -Hsh1. symmetry. by eapply lookup_delete_ne; last done.  done. }
    assert (r ## collect
              (λ (_ : ip_address)
                 (Sn0 : gmap socket_handle (socket * gset message)),
               collect
                 (λ (_ : socket_handle) (sr : socket * gset message), sr.2) Sn0)
              (delete ip S)) as Hdisj2.
    {  apply elem_of_disjoint. intros m Hmr Hmc.
       apply elem_of_collect in Hmc as (ip1 & Sn1 & HSn1 & Hmc).
       apply elem_of_collect in Hmc as (sh1 & (skt1, r1) & Hsh1 & Hm1).
       simplify_eq /=. ddeq ip ip1. rewrite lookup_delete_ne in HSn1; last done.
       assert (ip = ip1); last done.
       assert (is_Some (saddress skt)) as (s & HsktS).
       { destruct (saddress skt) eqn:Hskt; first by naive_solver.
         assert (r = ∅); last set_solver.
         destruct (Hcoh ip Sn Hip) as (Hhcoh & Hacoh & Hmcoh & Hrcoh).
         apply (Hrcoh sh skt r HSn); eauto. }
       assert (is_Some (saddress skt1)) as (s1 & HsktS1).
       { destruct (saddress skt1) eqn:Hskt; first by naive_solver.
         assert (r1 = ∅); last set_solver.
         destruct (Hcoh ip1 Sn1 HSn1) as (Hhcoh & Hacoh & Hmcoh & Hrcoh).
         apply (Hrcoh sh1 skt1 r1); eauto. }
       transitivity (ip_of_address (m_destination m)).
       + edestruct (Hcoh ip Sn Hip ) as (Hhcoh & Hacoh & Hmcoh & Hrcoh).
         symmetry. eapply Hacoh; eauto. rewrite HsktS. f_equal.
         symmetry. by eapply (Hmcoh sh skt r s HSn).
       + edestruct (Hcoh ip1 Sn1 HSn1 ) as (Hhcoh & Hacoh & Hmcoh & Hrcoh).
         eapply Hacoh; eauto. rewrite HsktS1. f_equal. symmetry.
         eapply (Hmcoh sh1 skt1 r1 s1); last done. rewrite -Hsh1; eauto. done. }
    assert (collect
              (λ (_ : socket_handle)
                 (sr : socket * gset message), sr.2) (delete sh Sn)
              ## collect
              (λ (_ : ip_address)
                 (Sn0 : gmap socket_handle (socket * gset message)),
               collect
                 (λ (_ : socket_handle) (sr : socket * gset message), sr.2) Sn0)
              (delete ip S)) as Hdisj3.
    { apply elem_of_disjoint.
      intros m Hmr Hmc.
      apply elem_of_collect in Hmc as (ip1 & Sn1 & HSn1 & Hmc).
      apply elem_of_collect in Hmc as (sh1 & (skt1, r1) & Hsh1 & Hm1).
      apply elem_of_collect in Hmr as (sh2 & (skt2, r2) & Hsh2 & Hm2).
      simpl in *. ddeq ip ip1. rewrite lookup_delete_ne in HSn1; last done.
      ddeq sh sh2. rewrite lookup_delete_ne in Hsh2; last done.
      assert (is_Some (saddress skt1)) as (s & HsktS1).
      { destruct (saddress skt1) eqn:Hskt; first by naive_solver.
        assert (r1 = ∅); last set_solver.
        destruct (Hcoh ip1 Sn1 HSn1) as (Hhcoh & Hacoh & Hmcoh & Hrcoh).
        apply (Hrcoh sh1 skt1 r1); eauto. }
      assert (is_Some (saddress skt2)) as (s1 & HsktS2).
      { destruct (saddress skt2) eqn:Hskt; first by naive_solver.
        assert (r2 = ∅); last set_solver.
        destruct (Hcoh ip Sn Hip) as (Hhcoh & Hacoh & Hmcoh & Hrcoh).
        apply (Hrcoh sh2 skt2 r2); eauto. }
      assert (ip = ip1); last done.
      transitivity (ip_of_address (m_destination m)).
      + edestruct (Hcoh ip Sn Hip ) as (Hhcoh & Hacoh & Hmcoh & Hrcoh).
        symmetry. eapply Hacoh; eauto. rewrite HsktS2. f_equal.
        symmetry. by eapply Hmcoh.
      + edestruct (Hcoh ip1 Sn1 HSn1 ) as (Hhcoh & Hacoh & Hmcoh & Hrcoh).
        eapply Hacoh; eauto. rewrite HsktS1. f_equal.
        symmetry. eapply Hmcoh; eauto. }
    rewrite !set_diff_distr; eauto with set_solver.
    - rewrite set_eq_subseteq; split; set_solver.
    - set_solver.
    - by apply disjoint_union_l.
    - by apply disjoint_union_l; set_solver.
  Qed.

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

Lemma buffers_subseteq_update_socket_sblock S Sn ip sh skt r b:
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    buffers S ⊆ buffers (<[ip:=<[sh:=(skt<| sblock := b |>, r)]> Sn]> S).
  Proof.
    intros.
    intros m Hm.
    apply elem_of_collect in Hm as (ip1 & Sip1 & HSip1 & Hm).
    ddeq ip ip1.
    - apply elem_of_collect in Hm as (h1 & (s1, r1) & Hhsr1 & Hm).
      apply elem_of_collect.
      ddeq sh h1.
      + exists ip1, (<[h1:=(skt<| sblock := b |>, r)]> Sn).
        rewrite lookup_insert; eauto.
        split; first done.
        apply elem_of_collect.
        exists h1, (skt<| sblock := b |>, r). split; last set_solver.
        rewrite lookup_insert. eauto.
      + exists ip1, (<[sh:=(skt<| sblock := b |>, r)]> Sn).
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

  Lemma message_history_evolution_update_sblock S Sn ip M mh sh skt r  b:
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    mh = message_history_evolution
         M M S (<[ip:=<[sh:=(skt<| sblock := b |>, r)]> Sn]> S) mh.
 Proof.
    intros ??. rewrite /message_history_evolution.
    destruct mh as (R,T).
    rewrite !difference_diag_L !left_id_L. f_equal.
    rewrite subseteq_empty_difference_L; first set_solver.
    rewrite /buffers. simplify_eq /=.
    by eapply buffers_subseteq_update_socket_sblock.
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
     (∀ ip Sn,
        S !! ip = Some Sn →
        socket_handlers_coh Sn ∧
        socket_addresses_coh Sn ip ∧
        socket_messages_coh Sn ∧
        socket_unbound_empty_buf_coh Sn ip) →
    m ∈ r →
    R ⊆ mh.1 →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    ({[ m ]} ∪ R ∪ mh.1, mh.2) =
    message_history_evolution
      M M S  (<[ip :=<[sh:=(skt, r ∖ {[m]})]> Sn]> S) mh.
  Proof.
    intros Hcoh Hmr HR HS HSn.
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

End Aneris_AS.
