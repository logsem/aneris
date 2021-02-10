From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
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
  Context `{!anerisG Σ}.

   (* receive_buffers_coh *)
  Lemma receive_buffers_coh_alloc_socket σ mhγ s sh ip Sn :
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = None →
    receive_buffers_coh (state_sockets σ) mhγ →
    receive_buffers_coh (<[ip:=<[sh:=(s, ∅)]> Sn]> (state_sockets σ)) mhγ.
  Proof.
    rewrite /receive_buffers_coh.
    intros HSn HNone Hrbcoh ip' Sn' sh' skt' r' m' HSn' Hskt' Hm'.
    ddeq ip ip'.
    - ddeq sh sh'; [ done | by eapply Hrbcoh ].
    - by eapply Hrbcoh.
  Qed.

   (** messages_history_coh *)
  Lemma messages_history_coh_init ip ports :
    messages_history_coh ∅ {[ip := ∅]} (history_init ip ports).
  Proof.
    rewrite /messages_history_coh
            /message_soup_coh
            /receive_buffers_coh
            /messages_addresses_coh
            /messages_received_from_sent_coh.
    split; first set_solver.
    split; first by intros; simplify_map_eq.
    split.
    - intros ? ? ? Hgam.
      apply history_init_empty in Hgam as (?&?&Hrt).
      set_solver.
    - by rewrite history_init_received history_init_sent.
  Qed.

  Lemma messages_history_coh_alloc_node M S mh ip ports :
    history_init ip ports ##ₘ mh →
    messages_history_coh M S mh →
    messages_history_coh M (<[ip:=∅]>S) (history_init ip ports ∪ mh).
  Proof.
    intros Hdisj Hcoh.
  Admitted.
    (*
    generalize dependent mh.
    induction ports as [|p Hp Hpp IH] using set_ind_L.
    - rewrite /history_init gset_map_empty gset_to_gmap_empty.
      intros mh ?. rewrite left_id_L.
       rewrite /messages_history_coh
            /message_soup_coh
            /receive_buffers_coh
            /messages_addresses_coh
            /messages_received_from_sent_coh.
       intros (?&?&?&?).
       split_and!; [ set_solver | | | set_solver ].
      + admit.
      + admit.
    - intros mh'.
      assert ((history_init ip ({[p]} ∪ Hp) ∪ mh') =
              ((history_init ip Hp) ∪ ((history_init ip {[p]}) ∪ mh')))
        as ->.
      { assert ( history_init ip ({[p]} ∪ Hp) =
               history_init ip Hp ∪ (history_init ip {[p]})) as ->.
      { admit. }
          by rewrite map_union_assoc. }
      intros.
      apply IH.
      admit.
      (Hmcoh & Hrcoh & Hacoh & Hrscoh).
    split. Search "union" "gmap".
  Admitted.  *)

  Lemma messages_history_coh_deliver_message mhγ M S Sn Sn' ip sh skt a R m :
    m ∈ messages_to_receive_at a M →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, R) →
    Sn' = <[sh:=(skt, R ∪ {[m]})]> Sn →
    saddress skt = Some a →
    messages_history_coh M S mhγ →
    messages_history_coh M (<[ip:=Sn']> S) mhγ.
  Proof.
    rewrite /messages_history_coh.
    intros Hm HSn Hsh HSn' Hskt (Hmcoh & Hrcoh & Hacoh).
    split; eauto.
    split; last eauto.
    intros ip1 Sn1 sh1 skt1 r1 m1 HSn1 Hskt1 Hm1.
    destruct (decide (ip = ip1)) as [->|].
    - rewrite lookup_insert in HSn1.
      simplify_eq.
      destruct (decide (sh = sh1)) as [->|].
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
    unfold messages_history_coh.
    intros (Hmsh & Hrb & Hmac & Hmr).
    split_and!; [|done..].
    intros ? ?; eapply Hmsh; set_solver.
  Qed.

End state_interpretation.
