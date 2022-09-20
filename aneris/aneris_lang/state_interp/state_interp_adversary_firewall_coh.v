From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
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

End state_interpretation_lemmas.
