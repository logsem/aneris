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

  Lemma mapsto_messages_lookup_public fw_st σ (sa : socket_address) sag bs bt s q :
    firewall_st_coh fw_st σ ->
    sa ∈ sag ->
    firewall_auth fw_st -∗
    sag ⤳*p[ bs , bt ]{ q } s -∗
    ⌜sa ∈ state_public_addrs σ⌝.
  Proof.
    iIntros (Hcoh Hin) "Hauth Hmpt".
    iDestruct (firewall_auth_mapsto_agree with "Hauth Hmpt") as "%Hlook".
    iPureIntro.
    apply (Hcoh sa); eauto.
  Qed.

  Lemma mapsto_messages_lookup_private fw_st σ sa sag bs bt s q :
    firewall_st_coh fw_st σ ->
    sa ∈ sag ->
    firewall_auth fw_st -∗
    sag ⤳*[ bs , bt ]{ q } s -∗
    ⌜sa ∉ state_public_addrs σ⌝.
  Proof.
    iIntros (Hcoh Hsa) "Hauth Hmpt".
    iDestruct (firewall_auth_mapsto_agree with "Hauth Hmpt") as "%Hlook".
    iDestruct (firewall_auth_disj with "Hauth") as "%Heq".
    iPureIntro.
    intros contra.
    apply (Hcoh sa) in contra as [sag' [Hin Hpublic]].
    assert (sag = sag') as ->.
    { eapply (Heq sa sag sag'); eauto. }
    rewrite Hlook in Hpublic.
    inversion Hpublic; done.
  Qed.

  (* If we know that a saddr is adversarial, then we can obtain a resource showing
     that another arbitrary saddr in the same group is adversarial. *)
  Lemma adversary_saddr_adv_own_same_sag σ sags sag sa sa' :
    adversary_firewall_coh σ sags -∗
    socket_address_group_ctx sags -∗
    socket_address_group_own sag -∗
    ⌜sa ∈ sag⌝ -∗
    ⌜sa' ∈ sag⌝ -∗
    adversary_saddr_adv_own sa -∗
      adversary_firewall_coh σ sags ∗
      socket_address_group_ctx sags ∗
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
    iDestruct (adversary_auth_rev_lookup_adv with "Hadv_auth") as "[Hadv_auth #Hadv_own]";
      [done|].
    iFrame "Hadv_own Hsags_auth".
    iExists _, _; iFrame "#∗".
  Qed.

  Lemma adversary_saddr_adv_nonadv_own_same_sag σ sags sag sa sa' :
    adversary_firewall_coh σ sags -∗
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
    iDestruct (adversary_auth_rev_lookup_adv with "Hadv_auth") as "[Hadv_auth #Hadv_own]";
      [done|].
    iDestruct (adversary_saddr_adv_nonadv_own with "Hadv_own Hnonadv") as "?"; done.
  Qed.

  Lemma adversary_saddr_adv_own_equiv_sender σ sags sagT sagR m m' :
    adversary_firewall_coh σ sags -∗
    socket_address_group_ctx sags -∗
    socket_address_group_own sagT -∗
    ⌜m ≡g{sagT, sagR} m'⌝ -∗
    adversary_saddr_adv_own (m_sender m) -∗
      adversary_firewall_coh σ sags ∗
      socket_address_group_ctx sags ∗
      adversary_saddr_adv_own (m_sender m').
  Proof.
    iIntros "Hadv_coh Hsock_ctx #Hsock_own %Hequiv #Hadv_sender".
    destruct Hequiv as (Hin&Hin'&_).
    iApply (adversary_saddr_adv_own_same_sag _ _ _ (m_sender m) (m_sender m')
             with "Hadv_coh Hsock_ctx Hsock_own"); try (by iPureIntro || iFrame "#").
  Qed.

  Lemma adversary_saddr_adv_own_equiv_destination σ sags sagT sagR m m' :
    adversary_firewall_coh σ sags -∗
    socket_address_group_ctx sags -∗
    socket_address_group_own sagR -∗
    ⌜m ≡g{sagT, sagR} m'⌝ -∗
    adversary_saddr_adv_own (m_destination m) -∗
      adversary_firewall_coh σ sags ∗
      socket_address_group_ctx sags ∗
      adversary_saddr_adv_own (m_destination m').
  Proof.
    iIntros "Hadv_coh Hsock_ctx #Hsock_own %Hequiv #Hadv_dest".
    destruct Hequiv as (_&_&Hin&Hin'&_).
    iApply (adversary_saddr_adv_own_same_sag _ _ _ (m_destination m) (m_destination m')
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

  Lemma adversary_firewall_coh_config_step σ σ' sags :
    config_step σ σ' ->
    adversary_firewall_coh σ sags -∗
    adversary_firewall_coh σ' sags.
  Proof.
    iIntros (Hstep) "Hcoh".
    iDestruct "Hcoh" as (adv_map fw_st) "(?&?&?&?&?&%Hdel)".
    inversion Hstep; subst; iExists adv_map, fw_st.
    - (* receive *)
      iFrame.
      iPureIntro.
      intros ip skts sh' skt' msgs m'.
      simpl.
      intros Hlook Hlook' Hin' Hadv.
      destruct (decide (ip = n)) as [->|Hne]; simpl in *.
      + (* ip = n *)
        rewrite lookup_insert in Hlook.
        inversion Hlook; subst.
        destruct (decide (sh = sh')) as [->|Hne'].
        * (* sh = sh' *)
          rewrite lookup_insert in Hlook'.
          inversion Hlook'; subst.
          rewrite /public_ip_check in H4.
          rewrite elem_of_cons in Hin'.
          destruct Hin' as [->|Hin'].
          ** (* the message is the newly-arrived message *)
            exists a.
            split; [done|].
            apply elem_of_messages_to_receive in H.
            rewrite <- H.
            apply H4.
            done.
          ** (* an old message *)
            apply (Hdel _ _ _ _ _ _ H0 H1 Hin' Hadv).
        * (* sh <> sh' *)
          rewrite lookup_insert_ne in Hlook'; [|done].
          apply (Hdel _ _ _ _ _ _ H0 Hlook' Hin' Hadv).
      + (* ip <> n *)
        rewrite lookup_insert_ne in Hlook; [|done].
        apply (Hdel _ _ _ _ _ _ Hlook Hlook' Hin' Hadv).
    - (* drop *)
      iFrame; done.
  Qed.

  Lemma adversary_firewall_coh_init ips sags σ :
    state_adversaries σ = ∅ ->
    state_public_addrs σ = ∅ ->
    adversary_auth (gset_to_gmap None ips) -∗
    firewall_auth (gset_to_gmap FirewallStPrivate sags) -∗
    adversary_firewall_coh σ sags.
  Proof.
    iIntros (Hadve Hfwe) "Hadv Hfw".
    iExists (gset_to_gmap None ips), (gset_to_gmap FirewallStPrivate sags).
    iFrame.
    iPureIntro.
    split.
    { rewrite Hadve; done. }
    split.
    { rewrite /adversary_st_coh.
      rewrite Hadve.
      intros ip'; split.
      - intros Hin. exfalso.
        apply (not_elem_of_empty ip' Hin).
      - intros Hlook. exfalso.
          rewrite lookup_gset_to_gmap_Some in Hlook.
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
    intros ? ? ? ? ? ? ? ? ? Hin.
    exfalso; apply (not_elem_of_empty _ Hin).
  Qed.

  Lemma adv_st_coh_alloc (adv_map : adversary_map) (σ : state) (ip : ip_address) :
    let σ' := (σ <| state_heaps := <[ip:=∅]> (state_heaps σ) |>
                 <| state_sockets := <[ip:=∅]> (state_sockets σ) |>) in
    adversary_st_coh adv_map σ ->
    ip ∉ (state_adversaries σ) ->
    adversary_st_coh (<[ip := None]> adv_map) σ'.
  Proof.
    intros σ' Hcoh Hnotin ip'.
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
    - intros Hlook.
      apply Hcoh.
      rewrite lookup_insert_Some in Hlook.
      destruct Hlook as [[_ contra] | [_ Hlook]].
      { exfalso.
        inversion contra. }
      done.
  Qed.

  Lemma adversary_persistent_keys_insert_None M ip :
    M !! ip = None →
    adversary_persistent_keys (<[ip:=None]> M) = adversary_persistent_keys M.
  Proof.
    intros Hnone.
    rewrite /adversary_persistent_keys.
    rewrite map_filter_insert_False; last first.
    { destruct 1 as [advSt contra].
      inversion contra. }
    rewrite map_filter_delete delete_notin; [done|].
    rewrite map_filter_lookup_None; auto.
  Qed.

  Lemma adversary_auth_alloc adv_map ip :
    adv_map !! ip = None ->
    adversary_auth adv_map ==∗
    adversary_auth (<[ip := None]> adv_map).
  Proof.
    iIntros (Hlook) "[Hauth Hpers]".
    rewrite /adversary_auth /adversary_persistent_own.
    remember (adversary_st_to_cmra <$> adv_map) as elem.
    iMod ((own_update _ _ (● (<[ip := adversary_st_to_cmra None]> elem))) with "Hauth") as "Hauth".
    { eapply (auth_update_auth _ _ _).
      eapply alloc_local_update; [|done].
      subst.
      rewrite lookup_fmap.
      rewrite Hlook; done. }
    iModIntro.
    rewrite fmap_insert.
    rewrite Heqelem. iFrame.
    rewrite adversary_persistent_keys_insert_None; done.
  Qed.

  Lemma adversary_firewall_coh_alloc_node σ ip sags :
    let σ' := (σ <| state_heaps := <[ip:=∅]> (state_heaps σ) |>
                 <| state_sockets := <[ip:=∅]> (state_sockets σ) |>) in
    ip ∉ state_adversaries σ ->
    adversary_firewall_coh σ sags ==∗
    adversary_firewall_coh σ' sags.
  Proof.
    iIntros (σ' Hnotin) "Hcoh".
    rewrite /adversary_firewall_coh.
    iDestruct "Hcoh" as (adv_st fw_st) "(?&?&?&?&?&?)".
    iExists (<[ip := None]> adv_st), fw_st.
  Admitted.

End state_interpretation_lemmas.
