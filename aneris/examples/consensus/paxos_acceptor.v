From aneris.examples.consensus Require Import paxos_prelude.
Import RecordSetNotations.

Section paxos_acceptor.
  Context `{!anerisG (Paxos_model params) Σ}.
  Context `{!paxosG Σ params}.

  Lemma acceptor_send_1b (bal : Ballot) b (a : Acceptor) (p : Proposer) h s
        (maxVal : option (Ballot * Value)) :
    let ip := ip_of_address (`a) in
    s_is_ser proposer_serialization ($bal, $maxVal) s →
    (if b is Some bal' then bal > bal' else True) →
    {{{ inv paxosN paxos_inv ∗
        ([∗ set] p ∈ Proposers, p ⤇ proposer_si) ∗
        h ↪[ ip] udp_socket (Some (`a)) true ∗
        maxVal_frag a maxVal ∗
        maxBal_frag a b ∗
        msgs_elem_of (msg1a bal) }}}
      SendTo #(LitSocket h) #s #(`p) @[ip]
    {{{ RET #(String.length s);
        h ↪[ip] udp_socket (Some (`a)) true ∗
        maxVal_frag a maxVal ∗
        maxBal_frag a (Some bal) ∗
        msgs_elem_of (msg1b a bal maxVal) }}}.
  Proof.
    iIntros (? Hser ? Φ) "(#Hinv & #Hproposers & Hh & Hmv & Hmb & Hm) HΦ".
    wp_apply aneris_wp_atomic_take_step_model.
    iInv (paxosN) as (δ2) ">(Hfrag & Hmauth & HmaxBal & HmaxVal & Hmcoh & HbI)" "Hclose".
    iDestruct (msgs_elem_of_in with "Hmauth Hm") as %?.
    iDestruct (maxBal_valid with "HmaxBal Hmb") as %?.
    iDestruct (maxVal_valid with "HmaxVal Hmv") as %?.
    iModIntro.
    iExists δ2, (δ2 <| maxBal ::= λ mb, <[a := Some bal]>mb |>
                   <| msgs   ::= λ ms, ms ∪ {[msg1b a bal maxVal]} |>).
    iFrame. iSplit.
    { iPureIntro. right.
      eapply phase1b; [done|done|done|]. destruct b as [bal'|]; eauto. }
    iMod (msgs_update (msg1b a bal maxVal) with "Hmauth") as "[Hmauth #Hm2]".
    iMod (maxBal_update (Some bal) with "HmaxBal Hmb") as "[HmaxBal Hmb]".
    iDestruct (big_sepS_elem_of _ _ (`p) with "Hproposers") as "#Hp_si";
      [auto|].
    iDestruct "Hmcoh" as (F' Ts) "(Has & Hps & -> & %HMagree)".
    iDestruct (big_sepS_delete _ _ (`a) with "Has") as "[[% Ha] Has]"; [auto|].
    wp_apply (aneris_wp_pers_send with "[$Hh $Ha $Hp_si]"); [done|done| |].
    { iModIntro. iExists _, _, _. iFrame "Hm2". auto. }
    iIntros "[Hh Ha] Hfrag".
    iMod ("Hclose" with "[-Hmb Hmv Hh HΦ]") as "_"; last first.
    { iModIntro. iApply ("HΦ" with "[$]"). }
    iExists _. iModIntro. iFrame. iSplitR "HbI"; last first.
    { iApply ballot_inv_maxBal.
      iApply ballot_inv_send_not2a; [|done]. intros (?&?& [=]). }
    set (m' := udp_msg (`a) (`p) s).
    iExists (<[(`a) := {[m']} ∪ F' (`a)]>F'), _.
    rewrite (send_msg_notin _ Proposers); [|auto]. iFrame.
    iDestruct (send_msg_combine with "Ha Has") as "$"; [auto|].
    iSplit; [done|]. iPureIntro. simpl.
    apply messages_agree_add; [| |done].
    { apply elem_of_union; auto. }
    exists p. rewrite /m'. f_equal.
    rewrite /msg1b_ser /mval_ser; simpl.
    destruct_is_ser Hser.
    f_equal. simpl.
    destruct Hp2 as [(Heq1 & Heq2)|(w & s & Habs & (?&?&?&?&->&Hx1&Hx2&->) & ->)];
      destruct maxVal as [[??]|]; simplify_eq /=; [done|].
    f_equal. destruct_is_ser Hx1; destruct_is_ser Hx2. done.
  Qed.

  Lemma acceptor_send_2b (bal : Ballot) b (a : Acceptor) lv h s (val : Value) mv :
    let ip := ip_of_address (`a) in
    is_set Learners lv →
    s_is_ser learner_serialization ($bal, $val) s →
    (if b is Some bal' then bal ≥ bal' else True) →
    {{{ inv paxosN paxos_inv ∗
        ([∗ set] l ∈ Learners, l ⤇ learner_si) ∗
        h ↪[ ip] udp_socket (Some (`a)) true ∗
        maxVal_frag a mv ∗
        maxBal_frag a b ∗
        msgs_elem_of (msg2a bal val) }}}
      sendto_all_set #(LitSocket h) lv #s @[ip]
    {{{ RET #();
        h ↪[ip] udp_socket (Some (`a)) true ∗
        maxVal_frag a (Some (bal, val)) ∗
        maxBal_frag a (Some bal) ∗
        [∗ set] _ ∈ Learners, msgs_elem_of (msg2b a bal val) }}}.
  Proof.
    iIntros (?? Hser ? Φ) "(#Hinv & #Hlearners & Hh & Hmv & Hmb & #Hm) HΦ".
    wp_apply (wp_pers_sendto_all_take_step
                (True)%I
                (λ _, msgs_elem_of (msg2b a bal val))
                (λ ls,
                 if bool_decide (ls ≡ ∅)
                 then (maxVal_frag a mv ∗ maxBal_frag a b : iProp Σ)%I
                 else (maxVal_frag a (Some (bal, val)) ∗ maxBal_frag a (Some bal))%I)
                with "[] [$Hh Hmv Hmb]"); [done|done|eassumption| | |].
    { iIntros "!#" (l ?) "(_ & Hb & %Hl)".
      iInv (paxosN) as (δ) ">(Hfrag & Hmauth & HmaxBal & HmaxVal & Hmcoh & HbI)"
                           "Hclose".
      iDestruct (ballot_inv_shot with "Hm Hmauth HbI")
        as "(#Hshot & Hmauth & HbI)".
      iDestruct (msgs_elem_of_in with "Hmauth Hm") as %?.
      iMod (msgs_update (msg2b a bal val) with "Hmauth") as "[Hmauth #Hm2]".
      iModIntro.
      iDestruct (big_sepS_elem_of _ _ l with "Hlearners") as "#Hl_si"; [auto|].
      iDestruct "Hmcoh" as (F' Ts) "(Has & Hps & -> & %HM')".
      iDestruct (big_sepS_delete _ _ (`a) with "Has") as "[[% Ha] Has]"; [auto|].
      iExists _, _, _, _, δ, (δ <| maxBal ::= λ mb, <[a := Some bal]>mb |>
                             <| maxVal ::= λ mv, <[a := Some (bal, val)]>mv |>
                             <| msgs   ::= λ ms, ms ∪ {[msg2b a bal val]} |>).
      iFrame "Hfrag Ha Hl_si".
      case_bool_decide;
        iDestruct "Hb" as "[Hmv Hmb]";
        iDestruct (maxBal_valid with "HmaxBal Hmb") as %?;
        iDestruct (maxVal_valid with "HmaxVal Hmv") as %?.
      - iSplit.
        { iPureIntro. right.
          eapply phase2b; [done|done|]. destruct b as [bal'|]; eauto. }
        iSplit.
        { iExists a, bal, val. simpl. iFrame "Hshot Hm2". done. }
        iIntros "[Ha Hfrag]".
        iMod (maxBal_update (Some bal) with "HmaxBal Hmb") as "[HmaxBal Hmb]".
        iMod (maxVal_update _ (Some (bal, val)) with "HmaxVal Hmv") as "[HmaxVal Hmv]".
        iMod ("Hclose" with "[-Hmb Hmv]") as "_"; last first.
        { iModIntro. iSplit; [done|].
          rewrite bool_decide_eq_false_2; [|set_solver]. by iFrame. }
        iModIntro. iExists _. iFrame "Hfrag HmaxBal HmaxVal Hmauth".
        iSplitR "HbI"; last first.
        { iApply ballot_inv_maxBal_maxVal.
          iApply ballot_inv_send_not2a; [|done]. naive_solver. }
        set (m := {| m_sender := `a; m_destination := l;
                     m_protocol := _; m_body := s |}).
        iExists (<[(`a) := {[m]} ∪ F' (`a)]>F'), _. simpl.
        rewrite (send_msg_notin _ Proposers); [|auto]. iFrame.
        iDestruct (send_msg_combine with "Ha Has") as "$"; [auto|].
        iSplit; [done|]. iPureIntro.
        apply messages_agree_add; [| |done].
        { apply elem_of_union; auto. }
        exists (l ↾ Hl). destruct maxVal as [[??]|]; by destruct_is_ser Hser.
      - (* TODO: This case is almost copy/paste of the previous; can we generalize something? *)
        iSplit.
        { iPureIntro. right.
          eapply phase2b; [done|done|]. eauto. }
        iSplit.
        { iExists a, bal, val. simpl. iFrame "Hshot Hm2". done. }
        iIntros "[Ha Hfrag]".
        iMod (maxBal_update (Some bal) with "HmaxBal Hmb") as "[HmaxBal Hmb]".
        iMod (maxVal_update _ (Some (bal, val)) with "HmaxVal Hmv") as "[HmaxVal Hmv]".
        iMod ("Hclose" with "[-Hmb Hmv]") as "_"; last first.
        { iModIntro. iSplit; [done|].
          rewrite bool_decide_eq_false_2; [|set_solver]. by iFrame. }
        iModIntro. iExists _. iFrame "Hfrag HmaxBal HmaxVal Hmauth".
        iSplitR "HbI"; last first.
        { iApply ballot_inv_maxBal_maxVal.
          iApply ballot_inv_send_not2a; [|done]. naive_solver. }
        set (m := {| m_sender := `a; m_destination := l;
                     m_protocol := _; m_body := s |}).
        iExists (<[(`a) := {[m]} ∪ F' (`a)]>F'), _. simpl.
        rewrite (send_msg_notin _ Proposers); [|auto]. iFrame.
        iDestruct (send_msg_combine with "Ha Has") as "$"; [auto|].
        iSplit; [done|]. iPureIntro.
        apply messages_agree_add; [| |done].
        { apply elem_of_union; auto. }
        exists (l ↾ Hl). destruct maxVal as [[??]|]; by destruct_is_ser Hser. }
    { rewrite bool_decide_eq_true_2 //. iFrame.  }
    { rewrite bool_decide_eq_false_2; [|by apply Learners_nonempty].
      iIntros "(_ & Hh & [Hmv Hmf] & Hls)".
      iApply "HΦ". iFrame. }
  Qed.

  Lemma acceptor_spec (a : Acceptor) lv :
    let ip := ip_of_address (`a) in
    is_set Learners lv →
    inv paxosN paxos_inv -∗
    ([∗ set] a ∈ Learners, a ⤇ learner_si) -∗
    ([∗ set] p ∈ Proposers, p ⤇ proposer_si) -∗
    (`a) ⤇ acceptor_si -∗
    free_ports ip {[ port_of_address (`a) ]} -∗
    maxBal_frag a None -∗
    maxVal_frag a None -∗
    WP acceptor int_serializer lv #(`a) @[ip] {{ v, True }}.
  Proof.
    iIntros (ip ?) "#Hinv #Hlearners #Hproposers #Ha_si Hp HmaxBal HmaxVal".
    rewrite /acceptor.
    wp_pures.
    wp_socket h as "Hh". wp_let.
    wp_socketbind.
    wp_alloc lbal as "Hbal".
    wp_pures.
    wp_alloc lval as "Hval".
    do 4 wp_pure _.
    (* loop invariant *)
    iAssert (∃ b mb, maxBal_frag a b ∗ maxVal_frag a mb ∗
                     lbal ↦[ip] $b ∗ lval ↦[ip] $mb)%I with "[-Hh]" as "Hloop".
    { iExists _, _. iFrame. simpl. iFrame. }
    wp_pure _.
    iLöb as "IH".
    iDestruct "Hloop" as (maxBal maxVal) "(Hmb & Hmv & Hlbal & Hlval)".
    wp_pures.
    wp_bind (ReceiveFrom _).
    iInv (paxosN) as (δ) ">(Hfrag & Hmsgs & HmaxBal & HmaxVal & Hmcoh & HbI)" "Hclose".
    iDestruct "Hmcoh" as (F Ts) "(Has & Hps & -> & %HM)".
    iDestruct (big_sepS_delete _ _ (`a) with "Has") as "[[% Ha] Has]"; [auto|].
    wp_apply (aneris_wp_pers_receivefrom with "[$Hh $Ha $Ha_si]");
      [done|done|done|].
    iIntros (m) "(Hh & Ha & #Hm)".
    iMod ("Hclose" with "[-Hmb Hmv Hlbal Hlval Hh]") as "_".
    { iModIntro. iExists _. iFrame.
      iExists _, _. iFrame (HM) "Hps".
      iSplit; [|done].
      iDestruct (big_sepS_insert _ _ (`a) with "[Ha $Has]") as "Has";
        [set_solver|eauto|].
      rewrite -union_difference_singleton_L //.
      apply (proj2_sig a). }
    iModIntro.
    wp_apply wp_unSOME; [done|]; iIntros "_".
    wp_pures.
    iDestruct "Hm" as "(% & -> & [(%bal & % & Hm1) | (%bal & %val & % & Hm1)])".
    - (* a phase 1a message was received *)
      wp_apply (s_deser_spec acceptor_serialization); [done|]; iIntros "_".
      wp_pures.
      wp_load.
      destruct maxBal as [bal'|].
      + (* [maxBal] has been initialized *)
        wp_pures.
        wp_apply wp_unSOME; [done|]; iIntros "_".
        wp_op.
        case_bool_decide; wp_if; last first.
        { wp_seq. iApply ("IH" with "Hh"). iExists _, _. by iFrame. }
        (* fresh ballot received greater than local [maxBal] *)
        wp_store. wp_load. wp_pures.
        wp_apply (s_ser_spec (proposer_serialization)).
        { iPureIntro. destruct maxVal as [[??]|]; apply serializable. }
        iIntros (s Hser).
        wp_apply (acceptor_send_1b bal with "[$Hinv $Hproposers $Hh $Hmb $Hmv $Hm1]");
          simpl; [done|lia|].
        iIntros "(Hh & Hmv & Hmb & #Hm2)". do 2 wp_seq.
        iApply ("IH" with "Hh"). iExists _, _. by iFrame.
      + (* [maxBal] uninitialized, no messages received before *)
        wp_pures.
        wp_store. wp_load. wp_pures.
        wp_apply (s_ser_spec (proposer_serialization)).
        { iPureIntro. destruct maxVal as [[??]|]; apply serializable. }
        iIntros (s Hser).
        wp_apply (acceptor_send_1b bal with "[$Hinv $Hproposers $Hh $Hmb $Hmv $Hm1]");
          [done|done|].
        iIntros "(Hh & Hmv & Hmb & Hm2)". do 2 wp_seq.
        iApply ("IH" with "Hh"). iExists _, _. by iFrame.
    - (* phase 2a message was received *)
      wp_apply (s_deser_spec acceptor_serialization); [done|]; iIntros "_".
      wp_pures.
      wp_load.
      destruct maxBal as [bal'|].
      + (* [maxBal] has been initialized *)
        wp_pures.
        wp_apply wp_unSOME; [done|]; iIntros "_".
        wp_op.
        case_bool_decide; wp_if; last first.
        { wp_seq. iApply ("IH" with "Hh"). iExists _, _. by iFrame. }
        (* ballot received, greater than or equal to local [maxBal] *)
        do 2 wp_store.
        wp_apply (s_ser_spec (learner_serialization)).
        { iPureIntro. apply serializable. }
        iIntros (s Hser).
        wp_apply (acceptor_send_2b bal with "[$Hinv $Hlearners $Hh $Hmb $Hmv $Hm1]");
          simpl; [done|done|lia|].
        iIntros "(Hh & Hmv & Hmb & #Hm2)".
        do 2 wp_seq.
        iApply ("IH" with "Hh"). iExists _, _. by iFrame.
      + (* [maxBal] uninitialized, no messages received before *)
        wp_pures.
        do 2 wp_store.
        wp_apply (s_ser_spec (learner_serialization)).
        { iPureIntro. apply serializable. }
        iIntros (s Hser).
        wp_apply (acceptor_send_2b bal with "[$Hinv $Hlearners $Hh $Hmb $Hmv $Hm1]");
          simpl; [done|done|lia|].
        iIntros "(Hh & Hmv & Hmb & #Hm2)".
        do 2 wp_seq.
        iApply ("IH" with "Hh"). iExists _, _. by iFrame.
  Qed.

End paxos_acceptor.
