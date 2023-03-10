From aneris.examples.consensus Require Import paxos_prelude.
Import RecordSetNotations.

Section paxos_proposer.
  Context `{!anerisG (Paxos_model params) Σ}.
  Context `{!paxosG Σ params}.

  Lemma recv_promises_spec p h (n : nat) (b : Ballot) :
    p ∈ Proposers →
    {{{ inv paxosN paxos_inv ∗ p ⤇ proposer_si ∗
        h ↪[ip_of_address p] (mkSocket (Some p) true) }}}
      recv_promises int_serializer #(LitSocket h) #n #b
      @[ip_of_address p]
    {{{ vp (promises : gset (option (Ballot * Value))) (senders : gset Acceptor),
        RET vp;
        h ↪[ip_of_address p] (mkSocket (Some p) true) ∗
        ⌜is_set promises vp⌝ ∗
        ⌜size senders = n⌝ ∗
        (∀ a, ⌜a ∈ senders⌝ -∗
               ∃ mv, ⌜mv ∈ promises⌝ ∗ msgs_elem_of (msg1b a b mv)) ∗
        (* TODO: better spec/implementation? - this is a bit silly *)
        (∀ mv, ⌜mv ∈ promises⌝ →
               ∃ a, ⌜a ∈ senders⌝ ∗ msgs_elem_of (msg1b a b mv)) }}}.
  Proof.
    iIntros (? Φ) "(#Hinv & #Hp_si & Hh) HΦ". rewrite /recv_promises.
    wp_pures.
    wp_apply (wp_set_empty (option (Ballot * Value))); [done|].
    iIntros (vp Hvp). wp_alloc lp as "Hlp".
    wp_pures.
    wp_apply (wp_set_empty Acceptor); [done|].
    iIntros (vs Hvs). wp_alloc ls as "Hls".
    do 4 wp_pure _.
    (* loop invariant *)
    iAssert (
        ∃ (promises : gset (option (Ballot * Value))) (senders : gset Acceptor) vp vs,
          lp ↦[ip_of_address p] vp ∗ ls ↦[ip_of_address p] vs ∗
             ⌜is_set promises vp⌝ ∗ ⌜is_set senders vs⌝ ∗
             (∀ a, ⌜a ∈ senders⌝ -∗
                    ∃ mv, ⌜mv ∈ promises⌝ ∗ msgs_elem_of (msg1b a b mv)) ∗
             (∀ mv, ⌜mv ∈ promises⌝ →
               ∃ a, ⌜a ∈ senders⌝ ∗ msgs_elem_of (msg1b a b mv)))%I
      with "[Hlp Hls]" as "Hloop".
    { iExists ∅, ∅, _, _. iFrame "∗%". iSplit; iIntros (? []%elem_of_empty). }
    clear Hvp Hvs vs vp. wp_pure _.
    iLöb as "IH".
    iDestruct "Hloop" as (promises senders vp vs) "(Hlp & Hls & %Hvp & %Hvs & Hincl & Hacc)".
    wp_pures.
    wp_load.
    wp_apply wp_set_cardinal; [done|]; iIntros "_".
    wp_op. case_bool_decide as Heq; wp_pures.
    { wp_load. iApply "HΦ". iFrame. apply Nat2Z.inj in Heq. by iFrame "%". }
    wp_bind (ReceiveFrom _).
    iInv (paxosN) as (δ) "(>Hfrag & >Hmauth & >Hbal & >Hval & Hmcoh & >HbI)"
                         "Hclose".
    iDestruct "Hmcoh" as ">Hmcoh".
    iDestruct "Hmcoh" as (F Ts) "(Has & Hps & -> & %HM)".
    iDestruct (big_sepS_delete _ _ p with "Hps") as "[[% Hp] Hps]"; [done|].
    wp_apply (aneris_wp_pers_receivefrom with "[$Hh $Hp $Hp_si]"); [done..|].
    iIntros (m) "(Hh & Hp & Hm)".
    iMod ("Hclose" with "[-Hh Hm Hlp Hls Hincl Hacc HΦ]") as "_".
    { iModIntro. iExists _. iFrame.
      iExists _, _. iFrame (HM) "Has".
      iSplit; [|done].
      iDestruct (big_sepS_insert _ _ p with "[Hp $Hps]")
        as "Hps"; [set_solver|eauto|].
      rewrite -union_difference_singleton_L //. }
    rewrite /proposer_si.
    iDestruct "Hm" as (?? mval Hser) "(-> & Hm)".
    iModIntro. wp_apply wp_unSOME; [done|]; iIntros "_".
    wp_pures.
    wp_apply (s_deser_spec proposer_serialization); [done|]; iIntros "_".
    wp_pures.
    case_bool_decide; wp_if; last first.
    { wp_seq. wp_apply ("IH" with "Hh HΦ [Hlp Hls Hincl Hacc]").
      iExists _, _, _, _. auto with iFrame. }
    simplify_eq.
    wp_load.
    wp_apply (wp_set_add $! Hvs). iIntros (vs' ?).
    wp_store. wp_load.
    wp_apply (wp_set_add $! Hvp).
    iIntros (vp' Hvp'). wp_store.
    wp_apply ("IH" with "Hh HΦ").
    iExists (_ ∪ _), (_ ∪ _), _, _. iFrame "Hlp Hls".
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { iIntros (mv). rewrite elem_of_union elem_of_singleton. iIntros ([-> | Hin]).
      - iExists _. iFrame. iPureIntro; set_solver.
      - iDestruct ("Hacc" $! mv Hin) as (a') "[% ?]".
        iExists a'. iFrame. iPureIntro; set_solver. }
    iIntros (a').
    rewrite elem_of_union elem_of_singleton.
    iIntros ([-> | ?]); last first.
    { iDestruct ("Hincl" $! a' with "[//]") as (mv') "[% H]".
      iExists mv'. iFrame. iPureIntro; set_solver. }
    iExists _. iFrame. iPureIntro; set_solver.
  Qed.

  Lemma find_max_promise_spec (lp : val)
        (promises : gset (option (Ballot * Value))) ip :
    is_set promises lp →
    {{{ True }}}
      find_max_promise lp @[ip]
    {{{ v, RET v;
        (⌜v = NONEV⌝ ∗ ⌜set_Forall (λ p, p = None) promises⌝) ∨
        (∃ (b : Ballot) (val : Value),
            ⌜Some (b, val) ∈ promises⌝ ∗
            ⌜v = SOMEV ($b, $val)⌝ ∗
            ⌜set_Forall (λ p, if p is Some (b', v')
                              then b ≥ b' else True) promises⌝) }}}.
  Proof.
    iIntros (? Φ) "_ HΦ". rewrite /find_max_promise.
    wp_pures.
    wp_apply (wp_set_foldl (A := option (Ballot * Value))
                (λ X v, (⌜v = NONEV⌝ ∗ ⌜set_Forall (λ p, p = None) X⌝) ∨
                        (∃ (b : Ballot) (val : Value),
                            ⌜Some (b, val) ∈ X⌝ ∗
                            ⌜v = SOMEV ($b, $val)⌝ ∗
                            ⌜set_Forall (λ p, if p is Some (b', v')
                                              then b ≥ b' else True) X⌝))%I
                (λ _, True%I) (λ _, True%I)).
    { iIntros ([[b v]|] acc X) "!#";
        iIntros (Ψ) "[[[-> %Hall] | (% & % & %Hin & -> & %Hall)] _] HΨ".
      - wp_pures. iApply "HΨ". iSplit; [|done]. iRight.
        iExists b, v. iPureIntro.
        split; [by apply elem_of_union_r, elem_of_singleton|].
        split; [done|].
        apply set_Forall_union.
        { apply (set_Forall_impl _ _ _ Hall). by intros ? ->. }
        apply set_Forall_singleton. lia.
      - wp_pures. case_bool_decide; wp_if.
        + iApply "HΨ". iPureIntro.
          split; [|done]. right.
          do 2 eexists.
          split; [apply elem_of_union_l, Hin|].
          split; [done|].
          apply set_Forall_union; [done|].
          apply set_Forall_singleton. lia.
        + iApply "HΨ". iPureIntro.
          split; [|done]. right.
          do 2 eexists.
          split; [by apply elem_of_union_r, elem_of_singleton|].
          split; [done|].
          apply set_Forall_union; [|apply set_Forall_singleton; lia].
          apply (set_Forall_impl _ _ _ Hall).
          intros [[]|]; [|done]. lia.
      - wp_pures. iApply "HΨ". iPureIntro.
        split; [|done]. left.
        split; [done|].
        apply set_Forall_union; [done|].
        by apply set_Forall_singleton.
      - wp_pures. iApply "HΨ". iPureIntro.
        split; [|done]. right.
        do 2 eexists.
        split; [by apply elem_of_union_l, Hin|].
        split; [done|].
        apply set_Forall_union; [done|].
        by apply set_Forall_singleton. }
    { iFrame "%". rewrite big_opS_unit; eauto. }
    iIntros (?) "[H _]". by iApply "HΦ".
  Qed.

  (* Definition bal (n : nat) (p : nat) := n * ProposersN + p. *)

  Lemma proposer_spec av h b (p : Proposer) (z : Value) :
    is_set Acceptors av →
    inv paxosN paxos_inv -∗
    ([∗ set] a ∈ Acceptors, a ⤇ acceptor_si) -∗
    (`p) ⤇ proposer_si -∗
    h ↪[ip_of_address (`p)] (mkSocket (Some (`p)) true) -∗
    pending b -∗
    WP proposer int_serializer av #(LitSocket h) #b #`z @[ip_of_address (`p)]
    {{ _, ∃ v, msgs_elem_of (msg2a b v) ∗
               h ↪[ip_of_address (`p)] (mkSocket (Some (`p)) true) }}.
  Proof.
    iIntros (?) "#Hinv #HA_sis #Hp_si Hh Hb".
    rewrite /proposer.
    wp_pures.
    wp_apply (s_ser_spec (acceptor_serialization)).
    { iPureIntro. apply serializable. }
    iIntros (s) "%Hser".
    (* send a phase 1a message to all acceptors, taking a step in the model for
       each message. *)
    wp_apply (wp_pers_sendto_all_take_step
                True%I
                (λ _, msgs_elem_of (msg1a _))
                (λ _, True)%I
                with "[] [$Hh //]"); [done|done|eassumption| |].
    { iIntros "!#" (a ?) "(_ & _ & %Ha)".
      set (m := {| m_sender := `p; m_destination := a; m_body := s |}).
      iInv (paxosN) as (δ) ">(Hfrag & Hmauth & Hbal & Hval & Hmcoh & HbI)" "Hclose".
      iMod (msgs_update (msg1a b) with "Hmauth") as "[Hmauth #Hm]".
      iModIntro.
      iDestruct "Hmcoh" as (F Ts) "(Has & Hps & -> & %HM)".
      iDestruct (big_sepS_delete _ _ (`p) with "Hps") as "[[% Hp] Hps]"; [auto|].
      iDestruct (big_sepS_elem_of _ _ a with "HA_sis") as "#Ha_si"; [done|].
      iExists _, _, _, _, δ, (δ <| msgs ::= λ ms, ms ∪ {[msg1a _]} |>).
      iFrame "#∗".
      iSplit.
      { iPureIntro. right. constructor. }
      iSplitR.
      { iExists p. iSplit; [done|]. iLeft. iExists _. iFrame "% #". }
      iIntros "(Hp & Hfrag)".
      iMod ("Hclose" with "[-]"); [|done].
      iModIntro. iExists _. iFrame.
      iSplitR "HbI"; last first.
      { iApply (ballot_inv_send_not2a with "HbI"). naive_solver. }
      iExists (<[(`p) := {[m]} ∪ F (`p)]>F), _; simpl.
      rewrite send_msg_notin; [|auto].
      iFrame.
      iDestruct (send_msg_combine with "Hp Hps") as "$"; [auto|].
      iSplit; [done|].
      iPureIntro.
      apply messages_agree_add; [| |done].
      { apply elem_of_union; auto. }
      simpl. destruct_is_ser Hser.
      by exists p, (a ↾ Ha). }
    iIntros "(_ & Hh & _ & Helem)". wp_pures.
    wp_apply (wp_set_cardinal with "[//]"); iIntros "_".
    wp_pures.
    replace #(_ + 1) with #(size Acceptors / 2 + 1)%nat; last first.
    { do 2 f_equal. lia. }
    wp_apply (recv_promises_spec with "[$Hinv $Hp_si $Hh]"); [auto|].
    iIntros (vp promises senders) "(Hh & %Hvp & %Hsize & #Hmsgs & #Hacc)".
    wp_pures.
    (* find the maximum phase 1b message from the majority, if any *)
    wp_apply (find_max_promise_spec _ promises with "[//]"); [done|].
    iIntros (?) "[(-> & %Hpromises) | (%b0 & %z' & %Hin &-> & %Hall)]".
    - (* no value was proposed by the majority *)
      wp_pures.
      iMod (pend_update_shot b z with "Hb") as "#Hshot".
      wp_apply (s_ser_spec (acceptor_serialization)).
      { iPureIntro. apply serializable. }
      iIntros (s' Hser').
      (* send phase 2a decision to all acceptors *)
      wp_apply (wp_pers_sendto_all_take_step
                  True%I (λ _, msgs_elem_of (msg2a b z)) (λ _, True)%I
                  with "[Hmsgs] [$Hh]"); [done|done|eassumption| |].
      { iIntros "!#" (a _) "(_ & _ & %Ha)".
        iInv (paxosN) as (δ) ">(Hfrag & Hmauth & Hbal & Hval & Hmcoh & HbI)" "Hclose".
        iAssert (⌜∀ a, a ∈ senders →
                       ∃ mv, mv ∈ promises ∧ msg1b a b mv ∈ δ.(msgs)⌝)%I
          as "%Hsenders".
        { iIntros (a' Ha').
          iDestruct ("Hmsgs" $! a' Ha') as (mv) "[% Hm]".
          iDestruct (msgs_elem_of_in with "Hmauth Hm") as %?. eauto. }
        iMod (msgs_update (msg2a b z) with "Hmauth") as "[Hmauth #Hm]".
        iModIntro.
        iDestruct "Hmcoh" as (F Ts) "(Has & Hps & -> & %HM)".
        iDestruct (big_sepS_delete _ _ (`p) with "Hps") as "[[% Hp] Hps]"; [auto|].
        iDestruct (big_sepS_elem_of _ _ a with "HA_sis") as "#Ha_si"; [done|].
        set (m := {| m_sender := `p; m_destination := a; m_body := s' |}).
        (* this viewshift is used for all acceptors; here we destruct on whether
           we're considering the first (the 2a message has not been recorded in
           the model) or not. *)
        destruct (decide (msg2a b z ∈ δ.(msgs))).
        + iExists _, _, _, _, δ, δ.
          iFrame "Hfrag Hp Ha_si".
          iSplit; [auto|].
          iSplitR.
          { iExists p. iSplit; [done|]. iRight. iExists _, z. by iFrame "Hm". }
          iIntros "(Hp & Hfrag)".
          iMod ("Hclose" with "[-]") as "_"; [|auto].
          iModIntro. iExists _. simpl.
          assert ((msgs δ ∪ {[msg2a b z]}) = msgs δ) as -> by set_solver.
          iFrame.
          iExists (<[(`p) := {[m]} ∪ F (`p)]>F), _; iFrame.
          rewrite send_msg_notin; [|auto]. iFrame.
          iDestruct (send_msg_combine with "Hp Hps") as "$"; [auto|].
          iSplit; [done|]. iPureIntro.
          eapply messages_agree_duplicate; [done| |done].
          destruct_is_ser Hser'. by exists p, (a ↾ Ha).
        + iExists _, _, _, _, δ, (δ <| msgs ::= λ ms, ms ∪ {[msg2a _ z]} |>).
          iAssert (⌜¬ (∃ z', msg2a b z' ∈ msgs δ)⌝)%I as "%".
          { iIntros ([? Hz']).
            iSpecialize ("HbI" $! _ _ Hz').
            by iDestruct (shot_agree with "Hshot HbI") as %->. }
          iDestruct (frag_st_rtc with "Hfrag") as %Hrtc.
          iFrame "Hfrag Hp Ha_si".
          iSplit.
          { iPureIntro. right.
            eapply (phase2a _ _ _ senders).
            * done.
            * apply majority_show_quorum. rewrite Hsize. lia.
            * split.
              - intros a' Ha'.
                destruct (Hsenders a' Ha') as (mv &?&?).
                exists (msg1b a' b mv).
                rewrite !elem_of_PropSet. split; eauto.
              - left.
                rewrite set_equiv=> m'.
                rewrite !elem_of_PropSet.
                split; [|done].
                intros ([Hin1 (? &?&?& Ha')] & a' & [? ?]); simplify_eq.
                destruct (Hsenders a' Ha') as (? & Hprom & Hin2).
                (* N.B.: here we are explicitlty using a pure property of the
                   model to obtain the contradiction! *)
                specialize (msg1b_agree _ _ _ _ _ Hrtc Hin1 Hin2).
                rewrite (Hpromises _ Hprom).
                done. }
          iSplit.
          { iExists p. iSplit; [done|]. iRight. iExists _, z. by iFrame "Hm". }
          iIntros "[Hp Hfrag]".
          iMod ("Hclose" with "[-]") as "_"; [|auto].
          iModIntro. iExists _. iFrame "Hfrag Hmauth Hbal Hval".
          iSplitR "HbI"; last first.
          { iIntros (??).
            rewrite elem_of_union elem_of_singleton.
            iIntros ([?|?]); by [iApply "HbI"|simplify_eq]. }
          iExists (<[(`p) := {[m]} ∪ F (`p)]>F), _. simpl.
          rewrite send_msg_notin; [|auto]. iFrame.
          iDestruct (send_msg_combine with "Hp Hps") as "$"; [auto|].
          iSplit; [done|].
          iPureIntro.
          apply messages_agree_add; [| |done].
          { apply elem_of_union; auto. }
          destruct_is_ser Hser'. by exists p, (a ↾ Ha). }
      iIntros "(_ & Hh & _ & H2a)".
      iExists _. iFrame.
      destruct Acceptors_choose as [a ?].
      by iApply (big_sepS_elem_of _ _ a with "H2a").
    - (* a value has already been proposed *)
      wp_pures.
      wp_apply (s_ser_spec (acceptor_serialization)).
      { iPureIntro. apply serializable. }
      iIntros (s' Hser').
      iMod (pend_update_shot b z' with "Hb") as "#Hshot".
      wp_apply (wp_pers_sendto_all_take_step
                  True%I (λ _, msgs_elem_of (msg2a b z')) (λ _, True)%I
                  with "[Hmsgs] [$Hh]"); [done|done|eassumption| |].
      { iIntros "!#" (a _) "(_ & _ & %Ha)".
        iInv (paxosN) as (δ) ">(Hfrag & Hmauth & Hbal & Hval & Hmcoh & HbI)"
                                 "Hclose".
        iAssert (⌜∀ a, a ∈ senders →
                       ∃ mv, mv ∈ promises ∧ msg1b a b mv ∈ δ.(msgs)⌝)%I as "%Hsenders".
        { iIntros (a' Ha').
          iDestruct ("Hmsgs" $! a' Ha') as (mv) "[% Hm']".
          iDestruct (msgs_elem_of_in with "Hmauth Hm'") as %?. eauto. }
        iAssert (⌜∀ mv, mv ∈ promises →
                        ∃ a, a ∈ senders ∧ msg1b a b mv ∈ δ.(msgs)⌝)%I as "%Hpromises".
        { iIntros (mv Hmv).
          iDestruct ("Hacc" $! mv Hmv) as (a') "[% Hm']".
          iDestruct (msgs_elem_of_in with "Hmauth Hm'") as %?. eauto. }
        iMod (msgs_update (msg2a b z') with "Hmauth") as "[Hmauth #Hm]".
        iModIntro.
        iDestruct "Hmcoh" as (F Ts) "(Has & Hps & -> & %HM)".
        iDestruct (big_sepS_delete _ _ (`p) with "Hps") as "[[% Hp] Hps]"; [auto|].
        iDestruct (big_sepS_elem_of _ _ a with "HA_sis") as "#Ha_si"; [done|].
        set (m := {| m_sender := `p; m_destination := a; m_body := s' |}).
        destruct (decide ((msg2a b z') ∈ δ.(msgs))).
        + iExists _, _, _, _, δ, δ.
          iFrame "Hfrag Hp Ha_si".
          iSplit; [auto|].
          iSplit.
          { iExists p. iSplit; [done|]. iRight. iExists _, _. by iFrame "Hm". }
          iIntros "[Hp Hfrag]".
          iMod ("Hclose" with "[-]") as "_"; [|auto].
          iModIntro. iExists _. simpl.
          assert ((msgs δ ∪ {[msg2a b z']}) = msgs δ) as -> by set_solver.
          iFrame. iExists (<[(`p) := {[m]} ∪ F (`p)]>F), _.
          rewrite send_msg_notin; [|auto]. iFrame.
          iDestruct (send_msg_combine with "Hp Hps") as "$"; [auto|].
          iSplit; [done|]. iPureIntro.
          eapply messages_agree_duplicate; [done| |done].
          destruct_is_ser Hser'. by exists p, (a ↾ Ha).
        + iExists _, _, _, _, δ, (δ <| msgs ::= λ ms, ms ∪ {[msg2a b z']} |>).
          iAssert (⌜¬ (∃ z', msg2a b z' ∈ msgs δ)⌝)%I as "%".
          { iIntros ([? Hz']).
            iSpecialize ("HbI" $! _ _ Hz').
            by iDestruct (shot_agree with "Hshot HbI") as %->. }
          iDestruct (frag_st_rtc with "Hfrag") as %Hrtc.
          iFrame "Hfrag Hp Ha_si".
          iSplit.
          { iPureIntro. right.
            eapply (phase2a _ z' _ senders).
            * done.
            * apply majority_show_quorum. rewrite Hsize. lia.
            * split.
              - intros a' Ha'.
                destruct (Hsenders a' Ha') as (mv &?&?).
                exists (msg1b a' b mv).
                rewrite !elem_of_PropSet. split; eauto.
              - right.
                destruct (Hpromises _ Hin) as (a' & Ha' & Hm).
                eexists _; exists a', b0.
                repeat split; eauto.
                intros m' ((Hin1 &?&?&?& Hin') & ? & ([]&?)); simplify_eq.
                do 3 eexists. split; [done|].
                destruct (Hsenders _ Hin') as (mv & Hmv & Hin2).
                specialize (Hall _ Hmv).
                (* N.B.: here we are explicitlty using a pure property of the
                   model to finish the proof!  *)
                specialize (msg1b_agree _ _ _ _ _ Hrtc Hin1 Hin2) as ?.
                simplify_eq. done. }
          iSplitR.
          { iExists p. iSplit; [done|]. iRight. iExists _, z'. by iFrame "Hm". }
          iIntros "[Hp Hfrag]".
          iMod ("Hclose" with "[-]") as "_"; [|auto].
          iModIntro. iExists _. iFrame.
          iSplitR "HbI"; last first.
          { iIntros (??).
            rewrite elem_of_union elem_of_singleton.
            iIntros ([?|?]); by [iApply "HbI"|simplify_eq]. }
          iExists (<[(`p) := {[m]} ∪ F (`p)]>F), _; simpl.
          rewrite send_msg_notin; [|auto]. iFrame.
          iDestruct (send_msg_combine with "Hp Hps") as "$"; [auto|].
          iSplit; [done|].
          iPureIntro.
          apply messages_agree_add; [| |done].
          { apply elem_of_union; auto. }
          destruct_is_ser Hser'. by exists p, (a ↾ Ha). }
      iIntros "(_ & Hh & _ & H2a)".
      iExists _. iFrame.
      destruct Acceptors_choose as [a ?].
      by iApply (big_sepS_elem_of _ _ a with "H2a").
  Qed.

  Lemma proposer'_spec av i (p : Proposer) (z : Value) :
    i < size Proposers →             
    is_set Acceptors av →
    inv paxosN paxos_inv -∗
    ([∗ set] a ∈ Acceptors, a ⤇ acceptor_si) -∗
    unbound (ip_of_address (`p)) {[port_of_address (`p)]} -∗
    (`p) ⤇ proposer_si -∗
    pending_class i 0 -∗
    WP proposer' int_serializer av #(`p) #i #(size Proposers) #`z
       @[ip_of_address (`p)] {{ _, True }}.
  Proof.
    iIntros (??) "#Hinv #Has Hport #Hp Hi". rewrite /proposer'.
    wp_pures.
    wp_socket sh as "Hskt".
    wp_pures.
    wp_socketbind.
    wp_alloc l as "Hl".
    do 4 wp_pure _.
    (* loop invariant *)
    iAssert (∃ c, pending_class i c ∗ l ↦[ip_of_address (`p)] #c)%I
      with "[Hi Hl]" as "Hloop".
    { iExists 0. replace (#0%nat) with (#0) by f_equal. iFrame. }
    wp_pure _.
    iLöb as "IH".
    iDestruct "Hloop" as (b) "(Hi & Hl)".
    wp_pures.
    wp_load.
    wp_pures.
    iDestruct (pending_pend_split with "Hi") as "[Hi Hpend]"; [done|].                             
    replace (#(b * size Proposers + i)) with (#(b * size Proposers + i)%nat)
      by (do 2 f_equal; lia).
    wp_bind (proposer _ _ _ _ _)%E.
    wp_apply aneris_wp_wand_r. iSplitL "Hpend Hskt".
    { by wp_apply (proposer_spec with "Hinv Has Hp Hskt Hpend"). }
    iIntros (?) "(% & #? & Hskt)".
    wp_seq. wp_load. wp_op.
    wp_store.
    iApply ("IH" with "Hskt [-]").
    iExists _. iFrame.
    replace (#(b + 1)%nat) with (#(b + 1)) by (do 2 f_equal; lia).
    done.
  Qed.

End paxos_proposer.
