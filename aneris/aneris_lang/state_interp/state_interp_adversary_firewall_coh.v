From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap.
From aneris.aneris_lang Require Import resources.
From aneris.aneris_lang.state_interp Require Import state_interp_def.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(** * Helper lemmas for coherence of adversary and firewall state *)

Section state_interpretation_lemmas.
  Context `{!anerisG Mdl Σ}.

  Lemma mapsto_messages_lookup_public fw_st σ sag bs bt s q :
    firewall_st_coh fw_st σ ->
    firewall_auth fw_st -∗
    sag ⤳*⟨pub⟩[ bs , bt ]{ q } s -∗
    ⌜∀ sa, sa ∈ sag -> sa ∈ state_public_addrs σ⌝.
  Proof.
    iIntros (Hcoh) "Hauth Hmpt".
    iDestruct (firewall_auth_mapsto_agree with "Hauth Hmpt") as "%Hlook".
    iPureIntro.
    intros sa Hin.
    apply (Hcoh sa); eauto.
  Qed.

  Lemma mapsto_messages_lookup_private fw_st σ sag bs bt s q :
    firewall_st_coh fw_st σ ->
    firewall_auth fw_st -∗
    sag ⤳*[ bs , bt ]{ q } s -∗
    ⌜∀ sa, sa ∈ sag -> sa ∉ state_public_addrs σ⌝.
  Proof.
    iIntros (Hcoh) "Hauth Hmpt".
    iDestruct (firewall_auth_mapsto_agree with "Hauth Hmpt") as "%Hlook".
    iDestruct (firewall_auth_disj with "Hauth") as "%Heq".
    iPureIntro.
    intros sa Hsa contra.
    apply (Hcoh sa) in contra as [sag' [Hin Hpublic]].
    assert (sag = sag') as ->.
    { eapply (Heq sa sag sag'); eauto. }
    rewrite Hlook in Hpublic.
    inversion Hpublic; done.
  Qed.

  (* If we know that a saddr is adversarial, then we can obtain a resource showing
     that another arbitrary saddr in the same group is adversarial. *)
  Lemma adversary_saddr_adv_own_same_sag mh σ sags sag sa sa' :
    adversary_firewall_coh mh σ sags -∗
    socket_address_group_ctx sags -∗
    socket_address_group_own sag -∗
    ⌜sa ∈ sag⌝ -∗
    ⌜sa' ∈ sag⌝ -∗
    adversary_saddr_adv_own sa -∗
      adversary_saddr_adv_own sa'.
  Proof.
    iIntros "Hadv_coh Hsags_auth #Hsag %Hin %Hin' #Hset".
    iDestruct (socket_address_group_ctx_own_included with "Hsags_auth Hsag") as "%Hincl".
    iDestruct "Hadv_coh" as (adv_st fw_st) "(Hadv_auth&?&#Hsags&#Hadv_coh&?&?)".
    iPoseProof "Hadv_coh" as "%Hadv_coh".
    iPoseProof "Hsags" as "%Hsags".
    iDestruct (adversary_auth_lookup with "Hadv_auth Hset") as "%Hsa".
    apply Hadv_coh in Hsa.
    apply (Hsags _ _ _ Hincl Hin Hin') in Hsa.
    apply Hadv_coh in Hsa.
    iDestruct (adversary_auth_rev_lookup_adv with "Hadv_auth") as "$".
    done.
  Qed.

  Lemma adversary_saddr_adv_nonadv_own_same_sag mh σ sags sag sa sa' :
    adversary_firewall_coh mh σ sags -∗
    socket_address_group_ctx sags -∗
    socket_address_group_own sag -∗
    ⌜sa ∈ sag⌝ -∗
    ⌜sa' ∈ sag⌝ -∗
    adversary_saddr_adv_own sa -∗
    adversary_saddr_nonadv_own sa' -∗
    False.
  Proof.
    iIntros "Hadv_coh Hsags_auth #Hsag %Hin %Hin' #Hadv #Hnonadv".
    iDestruct (socket_address_group_ctx_own_included with "Hsags_auth Hsag") as "%Hincl".
    iDestruct "Hadv_coh" as (adv_st fw_st) "(Hadv_auth&?&#Hsags&#Hadv_coh&?&?)".
    iPoseProof "Hadv_coh" as "%Hadv_coh".
    iPoseProof "Hsags" as "%Hsags".
    iDestruct (adversary_auth_lookup with "Hadv_auth Hadv") as "%Hsa".
    apply Hadv_coh in Hsa.
    apply (Hsags _ _ _ Hincl Hin Hin') in Hsa.
    apply Hadv_coh in Hsa.
    iDestruct (adversary_auth_rev_lookup_adv with "Hadv_auth") as "#Hadv_own";
      [done|].
    iDestruct (adversary_saddr_adv_nonadv_own with "Hadv_own Hnonadv") as "?"; done.
  Qed.

  Lemma adversary_saddr_adv_own_equiv_sender mh σ sags sagT sagR m m' :
    adversary_firewall_coh mh σ sags -∗
    socket_address_group_ctx sags -∗
    socket_address_group_own sagT -∗
    ⌜m ≡g{sagT, sagR} m'⌝ -∗
    adversary_saddr_adv_own (m_sender m) -∗
      adversary_saddr_adv_own (m_sender m').
  Proof.
    iIntros "Hadv_coh Hsock_ctx #Hsock_own %Hequiv #Hadv_sender".
    destruct Hequiv as (Hin&Hin'&_).
    iApply (adversary_saddr_adv_own_same_sag _ _ _ _ (m_sender m) (m_sender m')
             with "Hadv_coh Hsock_ctx Hsock_own"); try (by iPureIntro || iFrame "#").
  Qed.

  Lemma adversary_saddr_adv_own_equiv_destination mh σ sags sagT sagR m m' :
    adversary_firewall_coh mh σ sags -∗
    socket_address_group_ctx sags -∗
    socket_address_group_own sagR -∗
    ⌜m ≡g{sagT, sagR} m'⌝ -∗
    adversary_saddr_adv_own (m_destination m) -∗
      adversary_saddr_adv_own (m_destination m').
  Proof.
    iIntros "Hadv_coh Hsock_ctx #Hsock_own %Hequiv #Hadv_dest".
    destruct Hequiv as (_&_&Hin&Hin'&_).
    iApply (adversary_saddr_adv_own_same_sag _ _ _ _ (m_destination m) (m_destination m')
             with "Hadv_coh Hsock_ctx Hsock_own"); try (by iPureIntro || iFrame "#").
  Qed.

  Lemma elem_of_messages_to_receive m sa M :
    m ∈ messages_to_receive_at_multi_soup sa M -> m_destination m = sa.
  Proof.
    intros H.
    rewrite /messages_to_receive_at_multi_soup in H.
    rewrite elem_of_filter in H.
    destruct H as [? ?].
    done.
  Qed.

  Lemma adversary_firewall_coh_config_step mh σ σ' sags :
    config_step σ σ' ->
    adversary_firewall_coh mh σ sags -∗
    adversary_firewall_coh mh σ' sags.
  Proof.
    iIntros (Hstep) "Hcoh".
    iDestruct "Hcoh" as (adv_map fw_st) "(?&?&?&%Hcoh&?&%Hdel)".
    inversion Hstep; subst; iExists adv_map, fw_st; simpl in *.
    - (* receive *)
      iFrame.
      iSplitL "".
      { iPureIntro.
        destruct Hcoh as [? ?].
        split; [|done].
        simpl.
        rewrite dom_insert_lookup_L; [done|].
        rewrite H0; done. }
      iPureIntro.
      apply Hdel.
    - (* drop *)
      iFrame.
      iSplitL "".
      { iPureIntro.
        destruct Hcoh as [? ?].
        split; done. }
      done.
  Qed.

  Lemma adversary_firewall_coh_init ip sags σ :
    state_adversaries σ = ∅ ->
    state_public_addrs σ = ∅ ->
    dom (state_sockets σ) = {[ip]} ->
    adversary_auth {[ip := false]} -∗
    firewall_auth (gset_to_gmap FirewallStPrivate sags) -∗
    adversary_firewall_coh (gset_to_gmap (∅, ∅) sags) σ sags.
  Proof.
    iIntros (Hadve Hfwe Hdom) "Hadv Hfw".
    iExists {[ip := false]}, (gset_to_gmap FirewallStPrivate sags).
    iFrame.
    iPureIntro.
    split.
    { rewrite Hadve; done. }
    split.
    { rewrite /adversary_st_coh.
      rewrite Hdom dom_singleton_L.
      split; [done|].
      rewrite Hadve.
      intros ip'; split.
      - intros Hin. exfalso.
        apply (not_elem_of_empty ip' Hin).
      - intros Hlook. exfalso.
        apply lookup_singleton_Some in Hlook.
        destruct Hlook as [_ Hlook].
        inversion Hlook. }
    split.
    { rewrite /firewall_st_coh.
      intros sa.
      rewrite Hfwe.
      split.
      - intros Hin.
        exfalso.
          apply (not_elem_of_empty _ Hin).
      - intros Hfw.
        exfalso.
        destruct Hfw as [sag [_ Hlook]].
        rewrite lookup_gset_to_gmap_Some in Hlook.
        destruct Hlook as [_ Hlook].
        inversion Hlook. }
    rewrite /firewall_delivery_coh.
    rewrite Hadve Hfwe.
    intros ? ? ? ? ? ? Hin.
    exfalso; apply (not_elem_of_empty _ Hin).
  Qed.

  Lemma adv_st_coh_alloc_nonadv (adv_map : gmap ip_address bool) (σ : state) (ip : ip_address) :
    let σ' := (σ <| state_heaps := <[ip:=∅]> (state_heaps σ) |>
                 <| state_sockets := <[ip:=∅]> (state_sockets σ) |>) in
    adversary_st_coh adv_map σ ->
    state_sockets σ !! ip = None ->
    adversary_st_coh (<[ip := false]> adv_map) σ'.
  Proof.
    intros σ' [Hdom Hcoh] Hlook.
    assert (ip ∉ state_adversaries σ) as Hnotin.
    { intros contra.
      assert (ip ∉ dom (state_sockets σ)) as Hnotin'.
      { intros contra'.
        apply elem_of_dom in contra' as [? Hlook'].
        rewrite Hlook in Hlook'.
        inversion Hlook'. }
      apply Hnotin'.
      apply Hcoh in contra.
      assert (ip ∈ dom adv_map) as Hin.
      { apply elem_of_dom.
        eauto. }
      rewrite Hdom in Hin.
      exfalso.
      apply Hnotin'; done. }
    split.
    { subst σ'.
      rewrite !dom_insert_L.
      rewrite Hdom; done. }
    intros ip'.
    assert (state_adversaries σ = state_adversaries σ') as <-; [done|].
    split.
    - intros Hin.
      destruct (decide (ip = ip')) as [->|Hne].
      { exfalso.
        apply Hnotin; auto. }
      rewrite lookup_insert_Some.
      right.
      split; [done|].
      apply Hcoh; done.
    - intros Hlook'.
      apply Hcoh.
      rewrite lookup_insert_Some in Hlook'.
      destruct Hlook' as [[_ contra] | [_ Hlook']].
      { exfalso.
        inversion contra. }
      done.
  Qed.

  Lemma adversary_firewall_coh_alloc_nonadv mh σ ip sags :
    let σ' := (σ <| state_heaps := <[ip:=∅]> (state_heaps σ) |>
                 <| state_sockets := <[ip:=∅]> (state_sockets σ) |>) in
    state_sockets σ !! ip = None ->
    adversary_firewall_coh mh σ sags ==∗
    adversary_firewall_coh mh σ' sags.
  Proof.
    iIntros (σ' Hnone) "Hcoh".
    rewrite /adversary_firewall_coh.
    iDestruct "Hcoh" as (adv_st fw_st) "(Hadvauth&?&?&%Hadvst&?&%Hdel)".
    iExists (<[ip := false]> adv_st), fw_st.
    iFrame.
    assert (adv_st !! ip = None) as HlookNone.
    { destruct Hadvst as [Hadvst _].
      rewrite -not_elem_of_dom.
      rewrite Hadvst.
      rewrite not_elem_of_dom.
      done. }
    iMod (adversary_auth_alloc with "Hadvauth") as "[Hadvauth _]"; [done|].
    iModIntro.
    iFrame.
    iPureIntro.
    split.
    - apply adv_st_coh_alloc_nonadv; [done|].
      destruct Hadvst as [Hdom Hadvst].
      rewrite -not_elem_of_dom.
      intros contra.
      rewrite -not_elem_of_dom in HlookNone.
      apply HlookNone.
      rewrite Hdom.
      done.
    - subst σ'.
      apply Hdel.
  Qed.

  Lemma adversary_firewall_coh_heap_update mh σ sags heaps :
    adversary_firewall_coh mh σ sags -∗
    adversary_firewall_coh mh (σ <| state_heaps := heaps |>) sags.
  Proof.
    iIntros "Hcoh".
    rewrite /adversary_firewall_coh.
    eauto.
  Qed.

  Lemma adversary_firewall_coh_sblock_update mh σ sags ip Sn sh skt r b :
    state_sockets σ !! ip = Some Sn ->
    Sn !! sh = Some (skt, r) ->
    let S := <[ip := <[sh:= (skt<| sblock := b|>, r)]> Sn]>(state_sockets σ) in
    let σ' := σ <| state_sockets := S |> in
    adversary_firewall_coh mh σ sags -∗
      adversary_firewall_coh mh σ' sags.
  Proof.
    iIntros (Hip Hsh) "Hcoh".
    iDestruct "Hcoh" as (adv_st fw_st) "(?&?&%Hsags&%Hadv&%Hfw&%Hdel)".
    destruct Hadv as [Hdom Hadv].
    iExists adv_st, fw_st.
    iFrame. iPureIntro.
    simpl.
    repeat (split; eauto; simpl).
    rewrite dom_insert_L.
    rewrite Hdom.
    apply elem_of_dom_2 in Hip.
    set_solver.
  Qed.

  Lemma adversary_firewall_coh_alloc_socket mh σ sags ip Sn sh s :
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = None →
    saddress s = None →
    let σ' := σ <| state_sockets :=
                <[ip:=<[sh:=(s, [])]> Sn]> (state_sockets σ) |> in
    adversary_firewall_coh mh σ sags -∗
      adversary_firewall_coh mh σ' sags.
  Proof.
    iIntros (Hip Hsh Haddr) "Hcoh".
    iDestruct "Hcoh" as (adv_st fw_st) "(Hadv&Hfw&%Hsags&[%Hdom %Hadv]&%Hfw&%Hdel)".
    iExists adv_st, fw_st.
    iFrame.
    iPureIntro.
    repeat (split; eauto; simpl).
    rewrite dom_insert_L.
    rewrite Hdom.
    apply elem_of_dom_2 in Hip.
    set_solver.
  Qed.

  Lemma adversary_firewall_coh_socketbind mh σ sags Sn sh s sa ps :
    state_sockets σ !! ip_of_address sa = Some Sn →
    Sn !! sh = Some (s, []) →
    state_ports_in_use σ !! ip_of_address sa = Some ps ->
    let σ' :=
      σ <| state_sockets :=
          <[ip_of_address sa :=<[sh:=(s <| saddress := Some sa |>, [])]> Sn]>
          (state_sockets σ) |>
        <| state_ports_in_use :=
          <[ip_of_address sa:={[port_of_address sa]} ∪ ps]> (state_ports_in_use σ) |> in
    adversary_firewall_coh mh σ sags -∗
      adversary_firewall_coh mh σ' sags.
  Proof.
    iIntros (Hip Hsh Haddr) "Hcoh".
    iDestruct "Hcoh" as (adv_st fw_st) "(Hadv&Hfw&%Hsags&[%Hdom %Hadv]&%Hfw&%Hdel)".
    iExists adv_st, fw_st.
    iFrame.
    iPureIntro.
    repeat (split; eauto; simpl).
    rewrite dom_insert_L.
    rewrite Hdom.
    apply elem_of_dom_2 in Hip.
    set_solver.
  Qed.

End state_interpretation_lemmas.
