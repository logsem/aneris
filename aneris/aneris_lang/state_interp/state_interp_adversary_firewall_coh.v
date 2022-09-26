From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap.
From aneris.aneris_lang.state_interp Require Import state_interp_def.

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

End state_interpretation_lemmas.
