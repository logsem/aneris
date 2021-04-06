From stdpp Require Import fin_maps gmap.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From aneris.aneris_lang Require Import aneris_lang notation network resources.
From aneris.aneris_lang.state_interp Require Import state_interp_def.
From aneris.aneris_lang.lib Require Import util.
From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  Lemma messages_resource_coh_init B :
    ⊢ messages_resource_coh (gset_to_gmap (∅, ∅) B).
  Proof.
    rewrite /messages_resource_coh messages_sent_init.
    by iApply big_sepS_empty.
  Qed.

  Lemma message_received_insert_sent_message a msg msg' R T mh :
    mh !! a = Some (R, T) →
    messages_addresses_coh mh →
    T ## messages_sent (delete a mh) →
    msg' ∈ T ∨ msg' ∈ messages_sent (delete a mh) →
    message_received msg' mh →
    message_received msg' (<[a:=(R, {[msg]} ∪ T)]> (delete a mh)).
  Proof.
    intros Hsrc  Hmcoh Hdisj Hmsg' Hrd.
    rewrite (insert_delete mh a).
    eapply message_received_insert; eauto.
    apply elem_of_collect in Hrd as (a' & (R',T') & Hdlt & Hrd).
    ddeq a' a.
    simplify_map_eq.
    right. apply elem_of_collect.
    exists a', (R',T'). simplify_map_eq.
    rewrite lookup_delete_ne; eauto.
  Qed.

  Lemma messages_resource_coh_send mh a R T msg ϕ :
    msg ∉ T →
    mh !! a = Some (R, T) →
    m_sender msg = a →
    messages_addresses_coh mh →
    m_destination msg ⤇ ϕ -∗
    messages_resource_coh mh -∗
    ϕ msg -∗
    messages_resource_coh (<[a:=(R, {[msg]} ∪ T)]> mh).
  Proof.
    rewrite /messages_resource_coh /=.
    iIntros (Hmt Hsrc Hmh Hmcoh) "#Hϕ Hcoh Hm".
    rewrite -(insert_delete mh a).
    rewrite messages_sent_insert.
    rewrite {1} (messages_sent_split a R T); last done.
    assert (T ## messages_sent (delete a mh)) as Hdisj.
    { by eapply messages_sent_dijsoint. }
    rewrite !big_sepS_union; last done.
    - rewrite big_sepS_singleton.
      iDestruct "Hcoh" as "(HcohT & Hcoh)".
      iSplitL "Hm HcohT".
      + iSplitL "Hm".
        * iLeft. eauto.
        * rewrite big_sepS_mono; first done.
           iIntros (msg' Hmsg') "[Htt | %Hrd]"; first by iLeft.
           iRight. iPureIntro.
           eapply message_received_insert_sent_message; eauto.
      + eauto with iFrame.
        rewrite delete_idemp.
        rewrite big_sepS_mono; first done.
        iIntros (msg' Hmsg') "[Htt | %Hrd]"; first by iLeft.
        iRight. iPureIntro.
        eapply message_received_insert_sent_message; eauto.
    - set_solver.
    - rewrite delete_idemp.
      apply disjoint_union_l.
      split; last done.
      apply elem_of_disjoint.
      intros m HmT Hms.
      erewrite elem_of_singleton in HmT.
      subst.
      apply elem_of_collect in Hms as (a' & (R',T') & Ha' & Ht).
      simplify_map_eq.
      ddeq a' (m_sender msg).
      erewrite lookup_delete_ne in Ha'; last done.
      destruct (Hmcoh a' R' T' Ha') as (_ & HT).
      specialize (HT msg Ht).
      done.
  Qed.

  Lemma messages_resource_coh_receive a b R T R' T' m mh :
    m_destination m = a →
    m_sender m = b →
    mh !! a = Some (R, T) →
    mh !! b = Some (R',T') →
    m ∉ R  →
    m ∈ T' →
    messages_addresses_coh mh →
    messages_resource_coh mh -∗
    messages_resource_coh (<[a:=({[m]} ∪ R, T)]> mh) ∗
    ∃ φ, m_destination m ⤇ φ ∗ ▷ φ m.
  Proof.
    iIntros (Hmd Hms Hmha Hmhb HmR HmT' Hmacoh).
    iIntros "Hrcoh". rewrite /messages_resource_coh.
    assert (messages_sent mh = messages_sent (<[a:=(R, T)]>mh)) as Heq.
    { apply insert_id in Hmha as Heq. by rewrite {1} Heq. }
    rewrite {1} Heq.
    assert ((messages_sent (<[a:=(R, T)]> mh) ∖ {[m]}) =
            (messages_sent (<[a:=({[m]} ∪ R, T)]> mh) ∖ {[m]})) as Hdelm.
    { by rewrite !messages_sent_insert. }
    assert (m ∈ messages_sent (<[a:=(R, T)]> mh)) as Hsent.
    { rewrite -Heq. apply elem_of_messages_sent. set_solver. }
    assert (m ∈ messages_sent (<[a:=({[m]} ∪ R, T)]> mh)) as Hsent2.
    { rewrite messages_sent_insert. by rewrite messages_sent_insert in Hsent. }
    assert (message_received m (<[a:=({[m]} ∪ R, T)]> mh) ) as Hrcd.
    { rewrite message_received_insert. left. set_solver. }
    assert (m ∉ messages_received mh) as Hnotrcd.
    { intro Habs. apply elem_of_messages_received in Habs
        as (sa & (R0, T0) & Hmh & Hm). simplify_map_eq.
      specialize (Hmacoh sa R0 T0) as (H1 & H2); first done.
      specialize (H1 m Hm). simplify_map_eq /=. set_solver. }
    iPoseProof (big_opS_delete
                  (fun m0 => ((∃ Φ, m_destination m0 ⤇ Φ ∗ ▷ Φ m0)
                           ∨ ⌜message_received m0 mh⌝))%I
                  (messages_sent (<[a:=(R, T)]> mh)) m) as "Hdel"; first done.
    iPoseProof ("Hdel" with "Hrcoh") as "([Hr|%Hr] & Hrcoh)"; last done.
    iPoseProof (big_opS_delete _
                 (messages_sent (<[a:=({[m]} ∪ R, T)]> mh)) m) as "Hdel2";
      first done. iFrame. rewrite {2} Hdelm. iApply "Hdel2". iSplitR; eauto.
    iApply (big_sepS_mono with "Hrcoh"). iIntros (msg Hmsg) "[Hm|%Hm]".
    - iLeft. iFrame.
    - iRight. iPureIntro. apply insert_id in Hmha. rewrite -Hmha in Hm.
      erewrite message_received_insert in Hm. rewrite message_received_insert.
      destruct Hm as [?|Hm]; simplify_map_eq /=; set_solver.
  Qed.

End state_interpretation.
