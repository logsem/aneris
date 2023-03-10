From aneris.examples.consensus Require Import paxos_prelude paxos_learner.
From aneris.aneris_lang.lib Require Import assert_proof.

Section paxos_client.
  Context `{!anerisG (Paxos_model params) Σ}.
  Context `{!paxosG Σ params}.

  Definition client_serialization :=
    prod_serialization ballot_serialization int_serialization.

  Definition client_si : socket_interp Σ :=
    (λ m, ∃ (Q : gset Acceptor) (bal : Ballot) (val : Value),
        ⌜s_is_ser client_serialization ($bal, $val) (m_body m)⌝ ∗
        ⌜QuorumA Q⌝ ∗ [∗ set] a ∈ Q, msgs_elem_of (msg2b a bal val))%I.

  Lemma client_spec c R T :
    inv paxosN paxos_inv -∗
    c ⤇ client_si -∗
    unbound {[c]} -∗
    c @ client_si ⤳# (R, T) -∗
    WP client int_serializer #c
       @[ip_of_address c] {{ v, ∃ (z : Value), ⌜v = $z⌝ }}.
  Proof.
    iIntros "#Hinv #Hc_si Hp Hc". rewrite /client.
    wp_pures.
    wp_socket h as "Hh". wp_let.
    wp_socketbind.
    wp_apply (aneris_wp_pers_receivefrom with "[$Hh $Hc $Hc_si]");
      [done|done|done|].
    iIntros (m1) "(Hh & Hc & (%Q1 & % & %val1 & % & %Hmaj1 & #HQ1))".
    wp_apply wp_unSOME; [done|]; iIntros "_".
    wp_pures.
    wp_apply (s_deser_spec client_serialization); [done|]; iIntros "_".
    wp_pures.
    wp_apply (wp_pers_wait_receivefrom (λ m, ⌜m_sender m ≠ m_sender m1⌝)%I
             with "[] [$Hh $Hc $Hc_si]").
    { iIntros (m Φ) "!# _ HΦ". wp_pures. iApply "HΦ".
      case_bool_decide as Hneq; simpl; [done|].
      iPureIntro. congruence. }
    iIntros (m2 R') "(Hh & Hc & %Hneq & (%Q2 & % & %val2 & % & %Hmaj2 & #HQ2))".
    wp_pures.
    wp_apply (s_deser_spec client_serialization); [done|]; iIntros "_".
    do 5 (wp_pure _).
    wp_apply wp_assert.
    iInv (paxosN) as (δ) ">(Hfrag & Hmauth & Hrest)" "Hclose".
    iDestruct (frag_st_rtc with "Hfrag") as %Hrtc.
    iAssert (⌜∀ a, a ∈ Q1 → VotedFor δ a _ val1⌝)%I as %HQ1.
    { iIntros (a Ha).
      iDestruct (big_sepS_elem_of _ _ a with "HQ1") as "Hm"; [done|].
      by iDestruct (msgs_elem_of_in with "Hmauth Hm") as %?. }
    iAssert (⌜∀ a, a ∈ Q2 → VotedFor δ a _ val2⌝)%I as %HQ2.
    { iIntros (a Ha).
      iDestruct (big_sepS_elem_of _ _ a with "HQ2") as "Hm"; [done|].
      by iDestruct (msgs_elem_of_in with "Hmauth Hm") as %?. }
    wp_pures.
    iMod ("Hclose" with "[Hfrag Hmauth Hrest]") as "_".
    { iModIntro. iExists _. iFrame. }
    iModIntro.
    assert (Chosen δ val1) as Hval1.
    { eexists. exists Q1. auto. }
    assert (Chosen δ val2) as Hval2.
    { eexists. exists Q2. auto. }
    (* We now apply the correctness theorem of the model: given messages from
       two majorities, their votes must agree on the same value *)
    rewrite -(paxos_correct δ val1 val2) //.
    rewrite bool_decide_eq_true_2 //.
    iSplit; [done|].
    iModIntro. wp_pures. eauto.
  Qed.

  Lemma learner'_spec (l : Learner) R T av (c : socket_address):
    let ip := ip_of_address (`l) in
    is_set Acceptors av →
    `l ⤇ learner_si -∗
    c ⤇ client_si -∗
    unbound {[ (`l) ]} -∗
    `l @ learner_si ⤳# (R, T) -∗
    WP learner' int_serializer av #(`l) #c @[ip] {{ v, True }}.
  Proof.
    iIntros (ip ?) "#Hl_si #Hc_si Hp Hl". rewrite /learner'.
    wp_pures.
    wp_socket h as "Hh". wp_let.
    wp_socketbind.
    wp_bind (learner _ _ _).
    wp_apply aneris_wp_wand_r. iSplitL.
    { by wp_apply (learner_spec with "Hl_si Hh Hl"). }
    iIntros (?) "(%&%&%&%&%& Hh & Hl & %&->&#?)".
    wp_pures.
    wp_apply (s_ser_spec (client_serialization)).
    { iPureIntro. apply serializable. }
    iIntros (??).
    wp_apply (aneris_wp_pers_send with "[$Hh $Hl $Hc_si]"); [done|done| |auto].
    rewrite /client_si.
    iModIntro. iExists _, _, _. iFrame "#". eauto.
  Qed.

End paxos_client.
