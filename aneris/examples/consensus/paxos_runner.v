From aneris.examples.consensus Require Import
     paxos_prelude paxos_acceptor paxos_proposer paxos_learner paxos_client.

Definition runner (z1 z2 : Z) : expr :=
  let: "a1" := MakeAddress #"a1" #80 in
  let: "a2" := MakeAddress #"a2" #80 in
  let: "a3" := MakeAddress #"a3" #80 in
  let: "l1" := MakeAddress #"l1" #80 in
  let: "l2" := MakeAddress #"l2" #80 in
  let: "p1"  := MakeAddress #"p1" #80 in
  let: "p2"  := MakeAddress #"p2" #80 in
  let: "c" := MakeAddress #"c" #80 in
  let: "acceptors" := {[ "a1"; "a2"; "a3" ]} in
  let: "learners" := {[ "l1"; "l2" ]} in
  Start "a1" (acceptor int_serializer "learners" "a1");;
  Start "a2" (acceptor int_serializer "learners" "a2");;
  Start "a3" (acceptor int_serializer "learners" "a3");;
  Start "l1" (learner' int_serializer "acceptors" "l1" "c");;
  Start "l2" (learner' int_serializer "acceptors" "l2" "c");;
  Start "p1" (proposer' int_serializer "acceptors" "p1" #0 #2 #z1);;
  Start "p2" (proposer' int_serializer "acceptors" "p2" #1 #2 #z2);;
  Start "c" (client int_serializer "c").


Section runner.
  Definition p1_addr := SocketAddressInet "p1" 80.
  Definition p2_addr := SocketAddressInet "p2" 80.
  Definition a1_addr := SocketAddressInet "a1" 80.
  Definition a2_addr := SocketAddressInet "a2" 80.
  Definition a3_addr := SocketAddressInet "a3" 80.
  Definition l1_addr := SocketAddressInet "l1" 80.
  Definition l2_addr := SocketAddressInet "l2" 80.
  Definition c_addr  := SocketAddressInet "c" 80.

  Definition acceptors : gset socket_address := {[ a1_addr; a2_addr; a3_addr ]}.
  Definition proposers : gset socket_address := {[ p1_addr; p2_addr ]}.
  Definition learners : gset socket_address := {[ l1_addr; l2_addr ]}.
  Definition addrs : gset socket_address := acceptors ∪ proposers ∪ learners ∪ {[c_addr]}.

  Definition ips : gset string := {[ "p1"; "p2"; "a1"; "a2"; "a3"; "l1"; "l2"; "c" ]}.

  Definition values : gset Z := {[ 41; 42 ]}%Z.

  Global Program Instance runner_topo : network_topo :=
    Build_network_topo acceptors proposers learners values _ _ _ _.
  Solve All Obligations with rewrite ?size_union ?size_singleton //; set_solver.

  Context `{!paxosG Σ runner_topo}.
  Context `{anerisG (Paxos_model runner_topo) Σ}.

  Lemma runner_spec :
    {{{ inv paxosN paxos_inv ∗
        ([∗ set] a ∈ acceptors, a ⤇ acceptor_si) ∗
        ([∗ set] p ∈ proposers, p ⤇ proposer_si) ∗
        ([∗ set] l ∈ learners, l ⤇ learner_si) ∗
        c_addr ⤇ client_si ∗
        ([∗ set] l ∈ learners, l ⤳ (∅, ∅)) ∗
        c_addr ⤳ (∅, ∅) ∗
        ([∗ set] ip ∈ ips, free_ip ip) ∗
        ([∗ set] a ∈ acceptors, ∃ prf, maxBal_frag (a ↾ prf) None ∗
                                    maxVal_frag (a ↾ prf) None) ∗
        pending_class 0 0 ∗ pending_class 1 0 }}}
        runner 41 42 @["system"]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Has_si & #Hps_si & #Hls_si & #Hc_si &
                  Hls & Hport & Hch & Hips & Hfrags & Hpend0 & Hpend1) HΦ".
    rewrite /runner.
    do 8 (wp_makeaddress; wp_let).
    wp_apply (wp_set_empty socket_address); [done|]; iIntros (??).
    wp_apply (wp_set_add with "[//]"); iIntros (??).
    wp_apply (wp_set_add with "[//]"); iIntros (??).
    wp_apply (wp_set_add with "[//]"); iIntros (? Has).
    rewrite union_empty_r_L union_assoc_L in Has.
    wp_let.
    wp_apply (wp_set_empty socket_address); [done|]; iIntros (??).
    wp_apply (wp_set_add with "[//]"); iIntros (??).
    wp_apply (wp_set_add with "[//]"); iIntros (? Hls).
    rewrite union_empty_r_L in Hls.
    wp_let.
    iDestruct (big_sepS_delete _ _ "p1" with "Hips") as "(Hp1 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "p2" with "Hips") as "(Hp2 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "a1" with "Hips") as "(Ha1 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "a2" with "Hips") as "(Ha2 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "a3" with "Hips") as "(Ha3 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "l1" with "Hips") as "(Hl1 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "l2" with "Hips") as "(Hl2 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "c" with "Hips") as "(Hc & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ l1_addr with "Hls") as "(Hl1h & Hls)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ l2_addr with "Hls") as "(Hl2h & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ a1_addr with "Has_si") as "(Ha1_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ a2_addr with "Has_si") as "(Ha2_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ a3_addr with "Has_si") as "(Ha3_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ p1_addr with "Hps_si") as "(Hp1_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ p2_addr with "Hps_si") as "(Hp2_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ l1_addr with "Hls_si") as "(Hl1_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ l2_addr with "Hls_si") as "(Hl2_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ a1_addr with "Hfrags") as "((% & Ha1_frag1 & Ha1_frag2) & Hfrags)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ a2_addr with "Hfrags") as "((% & Ha2_frag1 & Ha2_frag2) & Hfrags)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ a3_addr with "Hfrags") as "((% & Ha3_frag1 & Ha3_frag2) & _)"; [set_solver|].
    wp_apply (aneris_wp_start). iFrame "Ha1".
    iSplitR "Ha1_frag1 Ha1_frag2"; last first.
    { iIntros "!>".
      wp_apply (acceptor_spec (_ ↾ _) with "Hinv Hls_si Hps_si Ha1_si Hport Ha1_frag1 Ha1_frag2");
        [done|..]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Ha2".
    iSplitR "Ha2_frag1 Ha2_frag2"; last first.
    { iIntros "!> Hport".
      wp_apply (acceptor_spec (_ ↾ _) with "Hinv Hls_si Hps_si Ha2_si Hport Ha2_frag1 Ha2_frag2");
        [done|..]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Ha3".
    iSplitR "Ha3_frag1 Ha3_frag2"; last first.
    { iIntros "!> Hport".
      wp_apply (acceptor_spec (_ ↾ _) with "Hinv Hls_si Hps_si Ha3_si Hport Ha3_frag1 Ha3_frag2");
        [done|..]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Hl1".
    iSplitR "Hl1h"; last first.
    { iIntros "!> Hport".
      assert (l1_addr ∈ Learners) as Hin by set_solver.
      iPoseProof (mapsto_messages_pers_alloc _ learner_si with "Hl1h []") as "Hl1h"; [done|].
      wp_apply (learner'_spec (l1_addr ↾ Hin) with "Hl1_si Hc_si Hport Hl1h");
        [done|..]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Hl2".
    iSplitR "Hl2h"; last first.
    { iIntros "!> Hport".
      assert (l2_addr ∈ Learners) as Hin by set_solver.
      iPoseProof (mapsto_messages_pers_alloc _ learner_si with "Hl2h []") as "Hl2h"; [done|].
      wp_apply (learner'_spec (l2_addr ↾ Hin) with "Hl2_si Hc_si Hport Hl2h");
        [done|..]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Hp1".
    iSplitR "Hpend0"; last first.
    { iIntros "!> Hport".
      assert (p1_addr ∈ Proposers) as Hin by set_solver.
      assert (41%Z ∈ values) as H41 by set_solver.
      wp_apply (proposer'_spec _ _ (p1_addr ↾ Hin) (41%Z ↾ H41)
                  with "Hinv Has_si Hport Hp1_si Hpend0");
        [|done].
      rewrite ?size_union ?size_singleton; [lia|set_solver]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Hp2".
    iSplitR "Hpend1"; last first.
    { iIntros "!> Hport".
      assert (p2_addr ∈ Proposers) as Hin by set_solver.
      assert (42%Z ∈ values) as H42 by set_solver.
      wp_apply (proposer'_spec _ _ (p2_addr ↾ Hin) (42%Z ↾ H42)
                  with "Hinv Has_si Hport Hp2_si Hpend1");
        [|done].
      rewrite ?size_union ?size_singleton; [lia|set_solver]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Hc".
    iSplitR "Hch"; last first.
    { iIntros "!> Hport".
      iPoseProof (mapsto_messages_pers_alloc _ client_si with "Hch []") as "Hch"; [done|].
      wp_apply aneris_wp_wand_r.
      iSplitL; [wp_apply (client_spec with "Hinv Hc_si Hport Hch"); set_solver|].
      eauto. }
    by iApply "HΦ".
  Qed.

End runner.
