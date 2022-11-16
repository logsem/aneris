From aneris.examples.consensus Require Import paxos_prelude.
From aneris.aneris_lang.lib Require Import map_proof.

Import RecordSetNotations.

Section paxos_learner.
  Context `{!anerisG (Paxos_model params) Σ}.
  Context `{!paxosG Σ params}.

  Lemma learner_spec h (l : Learner) R T av :
    let ip := ip_of_address (`l) in
    is_set Acceptors av →
    `l ⤇ learner_si -∗
    h ↪[ip] (mkSocket (Some (`l)) true) -∗
    `l @ learner_si ⤳# (R, T) -∗
    WP learner int_serializer #(LitSocket h) av @[ip]
    {{ v, ∃ (Q : gset Acceptor) (bal : Ballot) (val : Value) R T,
            h ↪[ip] (mkSocket (Some (`l)) true) ∗
            `l @ learner_si ⤳# (R, T) ∗
            ⌜QuorumA Q⌝ ∗ ⌜v = $(bal, val)⌝ ∗
            [∗ set] a ∈ Q, msgs_elem_of (msg2b a bal val) }}.
  Proof.
    iIntros (??) "#Hl_si Hh Hl". rewrite /learner.
    wp_pures.
    wp_apply wp_set_cardinal; [done|]; iIntros "_".
    wp_pures.
    wp_apply (wp_map_empty Ballot val); [done|].
    iIntros (??).
    wp_alloc lv as "Hlv".
    do 4 wp_pure _.
    (* loop invariant *)
    iAssert (∃ m v, lv ↦[ip] v ∗ ⌜is_map v m⌝ ∗
                    [∗ map] bal ↦ xv ∈ m,
                    ∃ (X : gset Acceptor) val,
                      ⌜is_set X xv⌝ ∗ shot bal val ∗
                      ([∗ set] x ∈ X, msgs_elem_of (msg2b x bal val)))%I
      with "[Hlv]" as "H".
    { iExists ∅, _. iFrame. rewrite big_sepM_empty //. }
    wp_pure _.
    iLöb as "IH" forall (R T).
    iDestruct "H" as (d vd) "(Hlv & %Hd & Hmsgs)".
    wp_pures.
    wp_bind (ReceiveFrom _).
    wp_apply (aneris_wp_pers_receivefrom with "[$Hh $Hl $Hl_si]");
      [done|done|done|].
    iIntros (m) "(Hh & Hl & (%a & %b & %z & %Hser & -> & #Hshot & #Hm))".
    wp_apply wp_unSOME; [done|]; iIntros "_".
    wp_pures.
    wp_apply (s_deser_spec learner_serialization); [done|]; iIntros "_".
    wp_pures. wp_load. wp_pures.
    wp_apply (wp_map_lookup $! Hd).
    destruct (d !! b) as [p|] eqn:Heq; iIntros (? ->).
    - wp_pures.
      iDestruct (big_sepM_delete _ _ b p with "Hmsgs")
        as "[(%X & %v' & %HX & #Hshot' & #HX) Hmsgs]"; [done|].
      iDestruct (shot_agree with "Hshot Hshot'") as %<-.
      wp_apply (wp_set_add $! HX).
      iIntros (? HX').
      wp_pures.
      wp_apply wp_set_cardinal; [done|]; iIntros "_".
      wp_op.
      case_bool_decide as Hsize; wp_pures.
      + iExists ({[a]} ∪ X), _, _, _, _. iFrame. iSplit.
        { iPureIntro.
          apply majority_show_quorum.
          apply Nat2Z.inj_ge.
          rewrite Hsize. lia. }
        iSplit; [done|].
        destruct (decide (a ∈ X)).
        { by assert ({[a]} ∪ X = X) as -> by set_solver. }
        rewrite big_sepS_union ?big_sepS_singleton; [|set_solver].
        iFrame "#".
      + wp_apply (wp_map_insert $! Hd).
        iIntros (d' Hd').
        wp_store.
        wp_apply ("IH" with "Hh Hl").
        iExists (<[b:= _]> d), _. iFrame. iSplit; [done|].
        rewrite big_sepM_insert_delete.
        iFrame.
        iExists ({[a]} ∪ X), _. iFrame "#".
        iSplit; [done|].
        destruct (decide (a ∈ X)).
        { by assert ({[a]} ∪ X = X) as -> by set_solver. }
        rewrite big_sepS_union ?big_sepS_singleton; [|set_solver].
        iFrame "#".
    - wp_pures.
      wp_apply (wp_set_empty Acceptor); [done|].
      iIntros (? HX).
      wp_pures.
      wp_apply (wp_set_add $! HX).
      iIntros (? HX').
      wp_pures.
      wp_apply wp_set_cardinal; [done|]; iIntros "_".
      rewrite union_empty_r_L size_singleton.
      wp_op.
      case_bool_decide as Hsize; wp_pures.
      + iExists {[a]}, _, _, _, _.
        rewrite big_sepS_singleton //.
        iFrame "∗ #".
        iSplit; [|done].
        iPureIntro.
        apply majority_show_quorum.
        rewrite size_singleton. lia.
      + wp_apply (wp_map_insert $! Hd).
        iIntros (d' Hd').
        wp_store.
        wp_apply ("IH" with "Hh Hl").
        iExists (<[b:= _]> d), _. iFrame. iSplit; [done|].
        rewrite big_sepM_insert //.
        iFrame.
        iExists {[a]}, _.
        iFrame "#".
        rewrite union_empty_r_L in HX'.
        iSplit; [done|].
        rewrite big_sepS_singleton //.
  Qed.

End paxos_learner.
