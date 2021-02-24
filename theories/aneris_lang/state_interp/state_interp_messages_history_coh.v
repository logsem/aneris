From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
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
  Context `{!anerisG Mdl Σ}.

  (* receive_buffers_coh *)
  Lemma receive_buffers_coh_alloc_socket σ mh s sh ip Sn :
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = None →
    receive_buffers_coh (state_sockets σ) mh →
    receive_buffers_coh (<[ip:=<[sh:=(s, ∅)]> Sn]> (state_sockets σ)) mh.
  Proof.
    rewrite /receive_buffers_coh.
    intros HSn HNone Hrbcoh ip' Sn' sh' skt' r' m' HSn' Hskt' Hm'.
    ddeq ip ip'.
    - ddeq sh sh'; [ done | by eapply Hrbcoh ].
    - by eapply Hrbcoh.
  Qed.

  Lemma receive_buffers_coh_update_sblock σ mh sh skt r ip Sn b :
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    receive_buffers_coh (state_sockets σ) mh →
    receive_buffers_coh
      (<[ip:=<[sh:=({| sfamily := sfamily skt;
                       stype := stype skt;
                       sprotocol := sprotocol skt;
                       saddress := saddress skt;
                       sblock := b |}, r)]> Sn]> (state_sockets σ)) mh.
  Proof.
    rewrite /receive_buffers_coh.
    intros HSn HNone Hrbcoh ip' Sn' sh' skt' r' m' HSn' Hskt' Hm'.
    ddeq ip ip'.
    - ddeq sh sh'; [ eauto | by eapply Hrbcoh ].
    - by eapply Hrbcoh.
  Qed.

  Ltac mhc_unfold_all :=
    rewrite /messages_history_coh /message_soup_coh
            /receive_buffers_coh /messages_addresses_coh
            /messages_received_from_sent_coh.

   (** messages_history_coh *)
  Lemma messages_history_coh_init ip ports :
    messages_history_coh ∅ {[ip := ∅]} (history_init ip ports).
  Proof.
    mhc_unfold_all. split; first set_solver.
    split; first by intros; simplify_map_eq.
    split; last by rewrite history_init_received history_init_sent.
    intros ??? Hg. apply history_init_empty in Hg as (?&?&?); set_solver.
  Qed.

  Lemma messages_history_coh_alloc_node_aux M S mh ip :
    messages_history_coh M S mh →
    messages_history_coh M (<[ip:=∅]> S) mh.
  Proof.
    mhc_unfold_all. intros (?&?&?&?). split; first set_solver.
    split; last set_solver. intros ip0 ???????. ddeq ip ip0; set_solver.
  Qed.

  Lemma messages_history_coh_alloc_node_aux_2 M S mh ip p:
    history_init ip {[p]} ##ₘ mh →
    messages_history_coh M S mh →
    messages_history_coh M S (history_init ip {[p]} ∪ mh).
  Proof.
    rewrite history_init_singleton.
    intros Hdisj Hcoh. rewrite -insert_union_singleton_l.
    revert Hcoh. mhc_unfold_all.
    intros (H1 & H2 & H3 & H4).
    split_and!.
    - intros m Hm. apply H1 in Hm as (R & T & Hmh & Hmt).
      destruct (decide ((m_sender m) = (SocketAddressInet ip p))) as [Heq|Hneq].
      + rewrite Heq. rewrite lookup_insert. rewrite -Heq in Hdisj.
        decompose_map_disjoint. by rewrite Hdisj in Hmh.
      + rewrite lookup_insert_ne; last done. set_solver.
    -  intros ip0 Sn sh skt r m HS HSn Hmr.
       destruct (decide ((m_sender m) = (SocketAddressInet ip p))) as [Heq|Hneq].
       + rewrite Heq lookup_insert.
         specialize (H2 ip0 Sn sh skt r m HS HSn Hmr) as (R & T & Hmh & ?).
         simplify_map_eq. rewrite Heq in Hmh. by rewrite Hdisj in Hmh.
       + rewrite lookup_insert_ne; last done. set_solver.
    -  intros a ???. ddeq a (SocketAddressInet ip p); set_solver.
    - apply elem_of_subseteq.
      intros m. rewrite !elem_of_collect. intros (a & RT & Hlk & Hm).
      ddeq a (SocketAddressInet ip p); first done.
      assert (m ∈ messages_received mh).
      { apply elem_of_messages_received. set_solver. }
      assert (m ∈ messages_sent mh) as Hms by by set_solver.
      apply elem_of_messages_sent in Hms as (sa & rt & Hrt & Hmrt).
      exists sa, rt.  ddeq sa (SocketAddressInet ip p); last done.
      simplify_map_eq.
  Qed.

  Lemma messages_history_coh_alloc_node M S mh ip ports :
    history_init ip ports ##ₘ mh →
    messages_history_coh M S mh →
    messages_history_coh M (<[ip:=∅]>S) (history_init ip ports ∪ mh).
  Proof.
    generalize dependent mh. induction ports as [|p ps Hpp IH] using set_ind_L.
    - rewrite /history_init gset_map_empty gset_to_gmap_empty.
      intros mh ?. rewrite left_id_L. apply messages_history_coh_alloc_node_aux.
    - intros mh'. assert ((history_init ip ({[p]} ∪ ps) ∪ mh') =
              ((history_init ip ps) ∪ ((history_init ip {[p]}) ∪ mh'))) as ->.
      { assert ( history_init ip ({[p]} ∪ ps) =
               history_init ip ps ∪ (history_init ip {[p]})) as ->.
      { by apply history_init_singleton_union. }
          by rewrite map_union_assoc. }
      intros Hdisj Hcoh.
      rewrite history_init_singleton_union in Hdisj; last done.
        apply map_disjoint_union_l in Hdisj as [Hd1 Hd2].
      apply IH; last by apply messages_history_coh_alloc_node_aux_2.
      apply map_disjoint_union_r. split_and!; eauto.
      apply map_disjoint_dom_2. rewrite{2} /history_init.
        rewrite gset_map_singleton gset_to_gmap_singleton dom_singleton_L
                dom_gset_to_gmap. set_solver.
  Qed.

  Lemma messages_history_coh_socketbind M S Sn mh sh skt a:
    let ip := ip_of_address a in
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, ∅) →
    saddress skt = None →
    messages_history_coh M S mh →
    messages_history_coh
      M (<[ip:=(<[sh:=((skt <| saddress := Some a |>), ∅)]>Sn)]> S) mh.
  Proof.
    rewrite /messages_history_coh.
    intros HSn Hsh Hskt (Hmcoh & Hrcoh & Hacoh).
    split; eauto. split; last eauto.
    intros ip1 Sn1 sh1 skt1 r1 m1 HSn1 Hskt1 Hm1.
    destruct a as (ip & p). ddeq ip ip1; ddeq sh sh1; eauto.
  Qed.

  Lemma messages_history_coh_send mh M S Sn ip sh skt a r m R T :
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    saddress skt = Some a →
    m_sender m = a →
    mh !! a = Some (R, T) →
    messages_history_coh M S mh →
    messages_history_coh ({[m]} ∪ M) S (<[a:=(R, {[m]} ∪ T)]> mh).
  Proof.
    mhc_unfold_all.
    intros HSn Hsh Hskt Hma Hmh (Hmcoh & Hrcoh & Hacoh & Hsrcoh).
     split_and!.
     - intros m' [->%elem_of_singleton|]%elem_of_union.
       + subst. rewrite lookup_insert.
         exists R, ({[m]} ∪ T). set_solver.
       + destruct (decide (a = m_sender m')) as [->|].
         * rewrite lookup_insert. eauto with set_solver.
         * rewrite lookup_insert_ne; last done. eauto with set_solver.
     - intros ip1 Sn1 sh1 skt1 r1 m1 HSn1 Hskt1 Hm1.
       destruct (decide (a = m_sender m1)) as [->|].
       + subst. rewrite lookup_insert. eauto with set_solver.
       + rewrite lookup_insert_ne; last done. by eapply Hrcoh.
     - intros a' ???.
       ddeq a a'; set_solver.
     - apply elem_of_subseteq.
       intros m'.
       rewrite !elem_of_collect.
       intros (a' & (R',T') & Hlk & Hm).
       destruct (decide (a = a')) as [->|].
       + rewrite lookup_insert in Hlk.
         simplify_map_eq.
         assert (m' ∈ messages_received mh).
         { apply elem_of_messages_received. set_solver. }
         assert (m' ∈ messages_sent mh) as Hms by by set_solver.
         apply elem_of_messages_sent in Hms as (sa & rt & Hrt & Hmrt).
         ddeq sa (m_sender m).
         * exists (m_sender m), (R', {[m]} ∪ T).
           rewrite lookup_insert. set_solver.
         * exists sa, rt. rewrite lookup_insert_ne; last done.
           set_solver.
       + rewrite lookup_insert_ne in Hlk; last done.
         simplify_map_eq.
          assert (m' ∈ messages_received mh).
         { apply elem_of_messages_received. set_solver. }
         assert (m' ∈ messages_sent mh) as Hms by by set_solver.
         apply elem_of_messages_sent in Hms as (sa & rt & Hrt & Hmrt).
         destruct (decide (sa = m_sender m)) as [->|].
         * exists (m_sender m), (R, {[m]} ∪ T).
           rewrite lookup_insert. split; first done.
           destruct rt. simpl in *. simplify_map_eq /=. set_solver.
         * exists sa, rt. rewrite lookup_insert_ne; last done.
           set_solver.
  Qed.

  Lemma messages_history_coh_receive mh M S Sn ip sh skt a r m R T :
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    saddress skt = Some a →
    m ∈ r →
    mh !! a = Some (R, T) →
    messages_history_coh M S mh →
    messages_history_coh M (<[ip_of_address a:=<[sh:=(skt, r∖{[m]})]> Sn]> S) mh.
  Proof.
    mhc_unfold_all. intros HSn Hsh Hskt Hma Hmh (Hmcoh & Hrcoh & Hacoh & Hsrcoh).
    split_and!;[done| |done|done].
    intros ip1 Sn1 sh1 skt1 r1 m1 HSn1 Hskt1 Hm1.
    ddeq  ip1 (ip_of_address a); last eauto.
    ddeq sh1 sh; last eauto.
    ddeq m m1; [ eauto | by eapply Hrcoh; eauto; set_solver ].
  Qed.

  Lemma messages_history_coh_receive_2 mh M S Sn ip sh skt a r m R T :
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    saddress skt = Some a →
    m ∈ r →
    m_destination m = a →
    mh !! a = Some (R, T) →
    messages_history_coh M S mh →
    messages_history_coh M
                         (<[ip_of_address a:=<[sh:=(skt, r∖{[m]})]> Sn]> S)
                         (<[a:=({[m]} ∪ R, T)]>mh).
  Proof.
    mhc_unfold_all.
    intros HSn Hsh Hskt Hma Hdest Hmh (Hmcoh & Hrcoh & Hacoh & Hsrcoh).
    split_and!.
    - intros m' Hm'. clear Hdest.
      ddeq a (m_sender m'); eauto with set_solver.
    - intros ip1 Sn1 sh1 skt1 r1 m1 HSn1 Hskt1 Hm1.
      clear Hdest.
      destruct (decide (a = m_sender m1)) as [Heq|Hneq].
      + ddeq ip1 (ip_of_address a); last eauto.
        * ddeq sh1 sh; set_solver.
        * set_solver.
      + rewrite lookup_insert_ne.
        ddeq ip1 (ip_of_address a); last eauto.
        * ddeq sh1 sh.
          ** ddeq m m1; [ eauto | by eapply Hrcoh; eauto; set_solver ].
          ** set_solver.
        * done.
    - intros a' ???. ddeq a a'; eauto.
      split_and!.
      * intros m0  [->%elem_of_singleton|]%elem_of_union; first done.
          by eapply Hacoh.
      * by eapply Hacoh.
    - assert (messages_sent (<[a:=({[m]} ∪ R, T)]> mh) = messages_sent mh) as ->.
      { apply insert_id in Hmh. symmetry in Hmh. rewrite {2} Hmh.
        by rewrite !messages_sent_insert. }
      assert (messages_received (<[a:=({[m]} ∪ R, T)]> mh) =
              {[m]} ∪ R ∪ messages_received (delete a mh)) as ->.
      { rewrite /messages_received. by rewrite collect_insert. }
       apply insert_id in Hmh. symmetry in Hmh. rewrite {1} Hmh in Hsrcoh.
      assert (messages_received (<[a:=(R, T)]> mh) =
              R ∪ messages_received (delete a mh)) as Heq.
      { rewrite /messages_received. by rewrite collect_insert. }
      rewrite Heq in Hsrcoh.
      assert (m ∈ messages_sent mh) as Hm.
      { apply elem_of_collect.
        specialize (Hrcoh ip Sn sh skt r m HSn Hsh Hma) as (R'&T'&HRT').
        naive_solver. }
      set_solver.
  Qed.

  Lemma messages_history_coh_deliver_message mh M S Sn Sn' ip sh skt a R m :
    m ∈ messages_to_receive_at a M →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, R) →
    Sn' = <[sh:=(skt, R ∪ {[m]})]> Sn →
    saddress skt = Some a →
    messages_history_coh M S mh →
    messages_history_coh M (<[ip:=Sn']> S) mh.
  Proof.
    rewrite /messages_history_coh.
    intros Hm HSn Hsh HSn' Hskt (Hmcoh & Hrcoh & Hacoh).
    split; eauto. split; last eauto.
    intros ip1 Sn1 sh1 skt1 r1 m1 HSn1 Hskt1 Hm1.
    destruct (decide (ip = ip1)) as [->|].
    - rewrite lookup_insert in HSn1.
      simplify_eq. destruct (decide (sh = sh1)) as [->|].
      + rewrite lookup_insert in Hskt1; simplify_eq.
        apply elem_of_union in Hm1 as [Hm1| ->%elem_of_singleton].
        * eapply Hrcoh; eauto.
        * apply Hmcoh. set_solver.
      + rewrite lookup_insert_ne in Hskt1; eauto.
    - by rewrite lookup_insert_ne in HSn1; eauto.
  Qed.

  Lemma messages_history_drop_message σ mhγ m :
    messages_history_coh (state_ms σ) (state_sockets σ) mhγ →
    messages_history_coh (state_ms σ ∖ {[m]}) (state_sockets σ) mhγ.
  Proof.
    unfold messages_history_coh. intros (Hmsh & Hrb & Hmac & Hmr).
    split_and!; [|done..]. intros ? ?; eapply Hmsh; set_solver.
  Qed.

End state_interpretation.
