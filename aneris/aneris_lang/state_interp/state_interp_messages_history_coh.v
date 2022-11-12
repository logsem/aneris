From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From aneris.prelude Require Import collect gmultiset.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import
     aneris_lang network resources.
From aneris.aneris_lang.state_interp Require Import
     state_interp_def.
From aneris.algebra Require Import disj_gsets.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  (* receive_buffers_coh *)
  Lemma receive_buffers_coh_alloc_socket σ mh s sh ip Sn :
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = None →
    receive_buffers_coh (state_sockets σ) mh →
    receive_buffers_coh (<[ip:=<[sh:=(s, [])]> Sn]> (state_sockets σ)) mh.
  Proof.
    rewrite /receive_buffers_coh.
    intros HSn HNone Hrbcoh ip' Sn' sh' skt' r' m' HSn' Hskt' Hm'.
    ddeq ip ip'.
    - ddeq sh sh'; [ set_solver | by eapply Hrbcoh ].
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

  Local Ltac mhc_unfold_all :=
    rewrite /messages_history_coh /message_soup_coh
            /receive_buffers_coh /messages_addresses_coh
            /messages_received_from_sent_coh.

  (** messages_history_coh *)
  Lemma messages_history_coh_init ip B :
    all_disjoint B →
    set_Forall (λ x, x ≠ ∅) B →
    messages_history_coh ∅ {[ip := ∅]} (gset_to_gmap (∅, ∅) B).
  Proof.
    mhc_unfold_all. split; first set_solver.
    split; first by intros; simplify_map_eq.
    split.
    { rewrite dom_gset_to_gmap. split; [done|]. split; [done|].
      intros ???. rewrite lookup_gset_to_gmap_Some.
      intros [? [= <- <-]]. set_solver. }
    rewrite messages_received_init messages_sent_init //.
  Qed.

  Lemma messages_history_coh_alloc_node M S mh ip :
    messages_history_coh M S mh →
    messages_history_coh M (<[ip:=∅]> S) mh.
  Proof.
    mhc_unfold_all. intros (?&?&?&?). split; first set_solver.
    split; last set_solver. intros ip0 ???????. ddeq ip ip0; set_solver.
  Qed.

  Lemma messages_history_coh_socketbind M S Sn mh sh skt a:
    let ip := ip_of_address a in
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, []) →
    saddress skt = None →
    messages_history_coh M S mh →
    messages_history_coh
      M (<[ip:=(<[sh:=((skt <| saddress := Some a |>), [])]>Sn)]> S) mh.
  Proof.
    rewrite /messages_history_coh.
    intros HSn Hsh Hskt (Hmcoh & Hrcoh & Hacoh).
    split; eauto. split; last eauto.
    intros ip1 Sn1 sh1 skt1 r1 m1 HSn1 Hskt1 Hm1.
    destruct a as (ip & p). ddeq ip ip1; ddeq sh sh1; eauto.
  Qed.

  Lemma messages_history_coh_send mh M S Sn ip sh skt sa sag r m R T :
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    saddress skt = Some sa →
    m_sender m = sa →
    sa ∈ sag →
    mh !! sag = Some (R, T) →
    messages_history_coh M S mh →
    messages_history_coh ({[+ m +]} ⊎ M) S (<[sag:=(R, {[m]} ∪ T)]> mh).
  Proof.
    mhc_unfold_all.
    intros HSn Hsh Hskt <- Hsag Hmh (Hmcoh & Hrcoh & (Hdisj & Hne & Hacoh) & Hsrcoh).
    split_and!.
    - intros m' [->%gmultiset_elem_of_singleton|]%gmultiset_elem_of_disj_union.
      + eexists R,({[m]} ∪ T),_. split; [done|]. rewrite lookup_insert.
        set_solver.
      + destruct (Hmcoh m' H) as (R' & T' & sag' & Hsag' & Heq & Hin').
        destruct (decide (sag' = sag)) as [->|Hnin].
        * eexists _, _, _. split; [done|].
          rewrite lookup_insert. split; [done|]. set_solver.
        * eexists _, _, _. split; [done|].
          rewrite lookup_insert_ne; last done. eauto with set_solver.
    - intros ip1 Sn1 sh1 skt1 r1 m1 HSn1 Hskt1 Hm1.
      destruct (Hrcoh ip1 Sn1 sh1 skt1 r1 m1 HSn1 Hskt1 Hm1) as
          (R' & T' & sag' & Hsag' & Heq & Hin').
      destruct (decide (sag' = sag)) as [->|Hnin].
      + eexists _, _, _. split; [done|].
        rewrite lookup_insert.
        split; [done|]. set_solver.
      + eexists _, _, _. split; [done|].
        rewrite lookup_insert_ne; last done. eauto with set_solver.
    - rewrite dom_insert_lookup_L; [ by apply Hdisj | by eexists _ ].
    - rewrite dom_insert_lookup_L; [ by apply Hne | by eexists _ ].
    - intros sag' ???.
      ddeq sag sag'; set_solver.
    - apply elem_of_subseteq.
      intros m'.
      rewrite !elem_of_collect.
      intros (sag' & (R',T') & Hlk & Hm).
      destruct (decide (sag = sag')) as [->|].
      + rewrite lookup_insert in Hlk.
        simplify_map_eq.
        assert (m' ∈ messages_received mh).
        { apply elem_of_messages_received. set_solver. }
        assert (m' ∈ messages_sent mh) as Hms by by set_solver.
        apply elem_of_messages_sent in Hms as (sag & rt & Hrt & Hmrt).
        ddeq sag sag'.
        * exists sag', (R', {[m]} ∪ T).
          rewrite lookup_insert. set_solver.
        * eexists sag, rt. rewrite lookup_insert_ne; last done. set_solver.
      + rewrite lookup_insert_ne in Hlk; last done.
        simplify_map_eq.
        assert (m' ∈ messages_received mh).
        { apply elem_of_messages_received. set_solver. }
        assert (m' ∈ messages_sent mh) as Hms by by set_solver.
        apply elem_of_messages_sent in Hms as (sag'' & rt & Hrt & Hmrt).
        destruct (decide (sag'' = sag)) as [->|].
        * exists sag, (R, {[m]} ∪ T).
          rewrite lookup_insert. split; first done.
          destruct rt. simpl in *. simplify_map_eq /=. set_solver.
        * exists sag'', rt. rewrite lookup_insert_ne; last done.
          set_solver.
  Qed.

  Lemma messages_history_coh_receive mh M S Sn ip sh skt sa sag r m R T :
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r ++ [m]) →
    saddress skt = Some sa →
    sa ∈ sag →
    mh !! sag = Some (R, T) →
    messages_history_coh M S mh →
    messages_history_coh M (<[ip_of_address sa:=<[sh:=(skt, r)]> Sn]> S) mh.
  Proof.
    mhc_unfold_all.
    intros HSn Hsh Hskt Hsag Hmh
           (Hmcoh & Hrcoh & (Hdisj & Hne & Hacoh) & Hsrcoh).
    split_and!; try done.
    intros ip1 Sn1 sh1 skt1 r1 m1 HSn1 Hskt1 Hm1.
    ddeq ip1 (ip_of_address sa); last eauto.
    ddeq sh1 sh; last eauto.
    ddeq m m1; [ eapply Hrcoh =>//; set_solver | by eapply Hrcoh; eauto; set_solver ].
  Qed.

  Lemma messages_history_coh_receive_2 mh M S Sn ip sh skt sa sag r m R T :
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r ++ [m]) →
    saddress skt = Some sa →
    m_destination m = sa →
    sa ∈ sag →
    mh !! sag = Some (R, T) →
    messages_history_coh M S mh →
    messages_history_coh M (<[ip_of_address sa:=<[sh:=(skt, r)]> Sn]> S)
                           (<[sag:=({[m]} ∪ R, T)]>mh).
  Proof.
    mhc_unfold_all.
    intros HSn Hsh Hskt Hdest Hsag Hmh (Hmcoh & Hrcoh & (Hdisj & Hne & Hacoh) & Hsrcoh).
    split_and!.
    - intros m' Hm'. clear Hdest.
      destruct (Hmcoh m' Hm') as (R' & T' & sag' & Hsag' & Heq & Hin).
      ddeq sag sag'.
      + eexists _, _, _. split; [done|]. rewrite lookup_insert.
        eauto with set_solver.
      + eexists _, _, _. split; [done|]. rewrite lookup_insert_ne; [|done].
        eauto with set_solver.
    - intros ip1 Sn1 sh1 skt1 r1 m1 HSn1 Hskt1 Hm1.
      clear Hdest.
      ddeq ip1 (ip_of_address sa).
      + ddeq sh sh1.
        * destruct (Hrcoh ip Sn sh1 skt1 (r1++[m]) m1 HSn Hsh) as
            (R' & T' & sag' & Hsag' & Heq & Hin).
          { set_solver. }
          destruct (decide (sag' = sag)) as [->|Hne'].
          -- eexists _, _, _. split; [done|]. rewrite lookup_insert.
             split; [done|]. set_solver.
          -- eexists _, _, _. split; [done|]. rewrite lookup_insert_ne; [|done].
             split; [done|]. set_solver.
        * destruct (Hrcoh ip Sn sh1 skt1 r1 m1 HSn Hskt1 Hm1) as
              (R' & T' & sag' & Hsag' & Heq & Hin).
          destruct (decide (sag' = sag)) as [->|Hne'].
          -- eexists _, _, _. split; [done|].
             rewrite lookup_insert. split; [done|]. set_solver.
          -- eexists _, _, _. split; [done|].
             rewrite lookup_insert_ne; [|done]. split; [done|]. set_solver.
      + destruct (Hrcoh ip1 Sn1 sh1 skt1 r1 m1 HSn1 Hskt1 Hm1) as
            (R' & T' & sag' & Hsag' & Heq & Hin).
        destruct (decide (sag' = sag)) as [->|Hne'].
        -- eexists _, _, _. split; [done|]. rewrite lookup_insert.
           split; [done|]. set_solver.
        -- eexists _, _, _. split; [done|]. rewrite lookup_insert_ne; [|done].
           split; [done|]. set_solver.
    - rewrite dom_insert_lookup_L; [ by apply Hdisj | by eexists _ ].
    - rewrite dom_insert_lookup_L; [ by apply Hne | by eexists _ ].
    - intros sag' ???. ddeq sag sag'; eauto.
      split_and!.
      * intros m0  [->%elem_of_singleton|]%elem_of_union; first done.
        by eapply Hacoh.
      * by eapply Hacoh.
    - assert (messages_sent (<[sag:=({[m]} ∪ R, T)]> mh) = messages_sent mh) as ->.
      { apply insert_id in Hmh. symmetry in Hmh. rewrite {2} Hmh.
        by rewrite !messages_sent_insert. }
      assert (messages_received (<[sag:=({[m]} ∪ R, T)]> mh) =
              {[m]} ∪ R ∪ messages_received (delete sag mh)) as ->.
      { rewrite /messages_received. by rewrite collect_insert. }
      apply insert_id in Hmh. symmetry in Hmh. rewrite {1} Hmh in Hsrcoh.
      assert (messages_received (<[sag:=(R, T)]> mh) =
              R ∪ messages_received (delete sag mh)) as Heq.
      { rewrite /messages_received. by rewrite collect_insert. }
      rewrite Heq in Hsrcoh.
      assert (m ∈ messages_sent mh) as Hm.
      { apply elem_of_collect.
        specialize (Hrcoh ip Sn sh skt (r ++ [m]) m HSn Hsh ltac:(set_solver)) as (R'&T'&HRT').
        naive_solver. }
      set_solver.
  Qed.

  Lemma messages_history_coh_deliver_message mh M S Sn Sn' ip sh skt a R m :
    m ∈ messages_to_receive_at_multi_soup a M →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, R) →
    Sn' = <[sh:=(skt, m :: R)]> Sn →
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
        apply elem_of_cons in Hm1 as [->| Hm1].
        * apply Hmcoh.
          rewrite /messages_to_receive_at_multi_soup in Hm.
          revert Hm; rewrite elem_of_filter; intros [? ?%gmultiset_elem_of_dom] =>//.
        * subst. eapply Hrcoh; eauto.
      + rewrite lookup_insert_ne in Hskt1; eauto.
    - by rewrite lookup_insert_ne in HSn1; eauto.
  Qed.

  Lemma message_soup_coh_subseteq M N mhm :
    (∀ m, m ∈ M → m ∈ N) → message_soup_coh N mhm → message_soup_coh M mhm.
  Proof. intros Hle Hcoh m Hin. by apply Hcoh, Hle. Qed.

  Lemma messages_history_coh_duplicate_message M S mhm m :
    m ∈ M →
    messages_history_coh M S mhm → messages_history_coh (M ⊎ {[+ m +]}) S mhm.
  Proof.
    intros Hin (HMcoh&Hrbuf&Hacoh&Hrsfcoh).
    split; [|done]. eapply message_soup_coh_subseteq; [|done]. set_solver.
  Qed.

  Lemma messages_history_coh_drop_message σ S mhγ m :
    messages_history_coh (state_ms σ) S mhγ →
    messages_history_coh (state_ms σ ∖ {[+ m +]}) S mhγ.
  Proof.
    unfold messages_history_coh. intros (Hmsh & Hrb & Hmac & Hmr).
    split_and!; [|done..].
    intros m' Hm'; eapply Hmsh.
    eapply gmultiset_elem_of_subseteq; first done.
    apply gmultiset_difference_subseteq.
  Qed.

End state_interpretation.
