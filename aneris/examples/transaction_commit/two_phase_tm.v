From aneris.aneris_lang.lib Require Export
     assert_proof
     network_util_proof set_proof map_proof nodup_proof coin_flip_proof inject.
From aneris.examples.transaction_commit Require Import two_phase_prelude.

Section transaction_manager.
  Context `{!network_topo}.
  Context `{!anerisG (TC_model RMs) Σ, !tcG Σ}.

  Lemma wp_transaction_manager_recv_responses R T h l rcv vRMs :
    is_set RMs vRMs →
    {{{ pending ∗
        is_rcvset_log l R tm ∗
        wp_nodup_rcv rcv tm (mkSocket (Some tm) true) l ∗
        tm ⤳ (R, T) ∗
        h ↪[ip_of_address tm] mkSocket (Some tm) true ∗
        tm ⤇ tm_si }}}
      recv_responses rcv #(LitSocket h) vRMs @[ip_of_address tm]
    {{{ (b : bool) R', RET #b;
          pending ∗ tm ⤳ (R', T) ∗ h ↪[ip_of_address tm] mkSocket (Some tm) true ∗
          is_rcvset_log l R' tm ∗
          if b then [∗ set] rm ∈ RMs, rm ↦◯ PREPARED ∗ pending
          else ∃ rm, ⌜rm ∈ RMs⌝ ∗ rm ↦◯ ABORTED ∗ pending_discarded }}}.
  Proof.
    iIntros (HRMs Φ) "(Hpend & Hl & #Hrcv & Htm & Hh & #Hsi) HΦ". rewrite /recv_responses.
    do 8 wp_pure _.
    wp_apply (wp_set_empty socket_address); [done|]; iIntros (v Hv).
    iAssert (∃ prepared, ⌜is_set prepared v⌝ ∗
             [∗ set] rm ∈ prepared, rm ↦◯ (PREPARED : rm_stateO) ∗ pending)%I as "-#Hloop".
    { iExists _. eauto. }
    clear Hv.
    iLöb as "IH" forall (v R) "Hloop".
    iDestruct "Hloop" as (X) "[%HX Hprepared]".
    wp_pures.
    wp_apply wp_set_equal; [done|].
    iIntros ([] ?); simplify_eq.
    { wp_pures. iApply "HΦ".  iFrame. }
    wp_pures.
    wp_apply ("Hrcv" with "[$Hh $Htm $Hl $Hsi]").
    iIntros (m) "(Hh & Htm & Hm & Hl & % & %)".
    wp_pures.
    case_bool_decide.
    - wp_pures. wp_apply (wp_set_add $! HX).
      iIntros (X' HX').
      wp_apply ("IH" with "Hpend Hl Htm Hh HΦ").
      rewrite /tm_si.
      iDestruct "Hm" as "[% [(_ & Hal & Hpend) | [[% ?] | [% ?]]]]"; [|congruence..].
      iExists _. iFrame (HX').
      destruct (decide (m_sender m ∈ X)).
      { by assert ({[m_sender m]} ∪ X = X) as -> by set_solver. }
      iApply big_sepS_union; [set_solver|].
      rewrite big_sepS_singleton. iFrame.
    - wp_pures. iApply "HΦ".
      iDestruct "Hm" as "[% [(% & Hal & Hpend') | [(% & ? & Hshot) | (% & ? & Hdisc)]]]";
        [congruence| |].
      { iDestruct (pending_shot with "Hpend Hshot") as %[]. }
      iFrame. eauto.
  Qed.

  (** * Transaction manager spec *)
  Lemma transaction_manager_spec vRMs :
    is_set RMs vRMs →
    unbound {[tm]} -∗
    ([∗ set] rm ∈ RMs, rm ⤇ rm_si) -∗
    tm ⤇ tm_si -∗
    tm ⤳ (∅, ∅) -∗
    pending -∗
    WP transaction_manager #tm vRMs @[ip_of_address tm]
    {{ v, (⌜v = #("COMMITTED")⌝ ∗ [∗ set] rm ∈ RMs,  rm ↦◯ COMMITTED) ∨
          (⌜v = #("ABORTED")⌝   ∗ ∃ rm, ⌜rm ∈ RMs⌝ ∗ rm ↦◯ ABORTED) }}.
  Proof.
    iIntros (HRMs) "Hp #Hrmsis #Htm_si Htm Hpend".
    rewrite /transaction_manager.
    wp_pures. wp_socket h as "Hh". wp_pures. wp_socketbind.
    wp_apply (wp_nodup_init _ (mkSocket _ _)); [done..|].
    iIntros (l rcv) "[Hlog #Hrcv]". wp_let.
    (* sending "PREPARE" to all *)
    wp_apply (wp_sendto_all_set (λ _, rm_si) with "[$Hh $Htm]"); auto.
    { iFrame "%".
      iApply (big_sepS_impl with "Hrmsis").
      iIntros "!#" (??) "Hsi".
      iFrame. by iLeft. }
    iIntros (?) "[Hh Htm]". wp_seq.
    wp_apply (wp_transaction_manager_recv_responses
                with "[$Hh $Hpend $Hlog $Htm $Hrcv $Htm_si]"); [done|].
    iIntros ([] R') "(Hpend & Htm & Hh & Hlog & Hb)".
    - (* all RMs are prepared to commit *)
      wp_pures.
      iDestruct (big_sepS_sep with "Hb") as "[#Hprepared Hpends]".
      iMod (tm_shot_prepared with "Hpend Hpends") as "#Hshot".
      wp_apply (wp_sendto_all_set (λ _, rm_si) with "[$Hh $Htm]"); [done|done|..].
      { iFrame "%". iApply (big_sepS_impl with "Hrmsis").
        iIntros "!#" (??) "Hsi". iFrame.
        rewrite /rm_si /=. eauto. }
      iIntros (?) "(Hh & Htm)". wp_pures.
      wp_apply (wp_receivefrom_nodup_set with "[] Hrcv [$Hh $Htm_si $Htm $Hlog //]");
        [done..| |].
      { by iIntros "!#" (?) "[% ?]". }
      iIntros (d' vd' ?) "(%Hd' & %Hdom' & Hms & _ & Hh & Htm & Hlog)".
      wp_pures.
      iPoseProof (tm_rm_committed with "Hshot Hms") as "Hms".
      iDestruct (big_sepM_sep with "Hms") as "[Hb Hms]".
      wp_apply (wp_map_iter (λ _ b, ⌜b = "COMMITTED"⌝)%I
                            (λ _ _, True)%I True%I _ _ d' with "[] [$Hb //]").
      { iIntros (rm b Ξ) "!# [_ ->] HΞ". do 3 wp_pure _.
        wp_apply wp_assert. wp_pures. iSplit; [done|]. iModIntro. by iApply "HΞ". }
      iIntros "_".
      wp_seq. iLeft. iSplit; [done|].
      rewrite big_sepM_dom Hdom' //.
    - (* someone aborted *)
      wp_pures.
      iMod (pending_discard with "Hpend") as "#Hdisc".
      wp_apply (wp_sendto_all_set (λ _, rm_si) with "[$Hh $Htm]"); [done|done|..].
      { iFrame "%". iApply (big_sepS_impl with "Hrmsis").
        iIntros "!#" (??) "Hsi". iFrame. rewrite /rm_si; eauto. }
      iIntros (?) "[Hh Htm]". wp_pures.
      iRight.
      iDestruct "Hb" as (?) "(?&?&?)".
      eauto.
  Qed.

End transaction_manager.
