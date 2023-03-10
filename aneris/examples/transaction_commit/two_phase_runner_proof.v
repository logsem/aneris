From aneris.examples.transaction_commit Require Export
    two_phase_runner_code.
From aneris.examples.transaction_commit Require Import
    two_phase_runner_code two_phase_prelude two_phase_tm two_phase_rm.
(** * A simple runner (without aux. clients), proving safety  *)
Section runner.

  Open Scope nat_scope.
  Definition tm_addr := SocketAddressInet "tm" 80.
  Definition rm1_addr := SocketAddressInet "rm.01" 80.
  Definition rm2_addr := SocketAddressInet "rm.02" 80.
  Definition rm3_addr := SocketAddressInet "rm.03" 80.
  Definition rms : gset socket_address :=
    {[ rm1_addr; rm2_addr; rm3_addr ]}.
  Definition addrs : gset socket_address := {[ tm_addr ]} ∪ rms.
  Definition ips : gset string := {[ "tm"; "rm.01"; "rm.02"; "rm.03" ]}.

  Program Instance my_topo : network_topo :=
    {| RMs := rms; tm := tm_addr |}.
  Solve All Obligations with set_solver.

  Context `{!anerisG (TC_model rms) Σ, !tcG Σ}.

  Notation pending_frac := (dfrac_oneshot.pending tc_oneshot_gname).

  Lemma RMs_size :
    size RMs = 3.
  Proof. rewrite /RMs !size_union ?size_singleton //; set_solver. Qed.

  Lemma runner_spec :
    {{{ inv tcN tc_inv ∗
        tm_addr ⤇ tm_si ∗
        unbound {[rm1_addr;rm2_addr;rm3_addr;tm_addr]} ∗
        tm_addr ⤳ (∅, ∅) ∗
        ([∗ set] rm ∈ rms, rm ⤇ rm_si) ∗
        ([∗ set] rm ∈ rms, rm ↦●{1/2} WORKING) ∗
        ([∗ set] ip ∈ ips, free_ip ip) ∗
        pending_frac 1 }}}
      runner @["system"]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Htm_si & Hunbound & Htm_a & #Hrms_si & Hwork & Hips & Hpend) HΦ".
    rewrite /runner.
    do 4 (wp_makeaddress; wp_let).
    wp_apply (wp_set_empty socket_address); [done|]; iIntros (?) "%H".
    do 3 (wp_apply (wp_set_add (A := socket_address) with "[//]");
          iIntros (?) "%").
    wp_pures.
    rewrite (pending_split_N _ (size RMs + 1)); [|lia].
    iDestruct (big_sepS_delete _ _ "rm.01" with "Hips") as "(Hrm1 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "rm.02" with "Hips") as "(Hrm2 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "rm.03" with "Hips") as "(Hrm3 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "tm" with "Hips") as "(Htm & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ rm1_addr with "Hwork") as "(Hw1 & Hwork)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ rm2_addr with "Hwork") as "(Hw2 & Hwork)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ rm3_addr with "Hwork") as "(Hw3 & _)"; [set_solver|].
    rewrite RMs_size.
    iDestruct (big_sepS_delete _ _ 0 with "Hpend") as "(Hp1 & Hpend)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ 1 with "Hpend") as "(Hp2 & Hpend)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ 2 with "Hpend") as "(Hp3 & Hpend)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ 3 with "Hpend") as "(Ht & _)"; [set_solver|].
    rewrite -RMs_size.
    iDestruct (unbound_split with "Hunbound") as "[Hunbound Htm_b]"; [set_solver|].
    iDestruct (unbound_split with "Hunbound") as "[Hunbound Hrm3_b]"; [set_solver|].
    iDestruct (unbound_split with "Hunbound") as "[Hrm1_b Hrm2_b]"; [set_solver|].
    wp_apply aneris_wp_start; iFrame.
    iSplitR "Hw1 Hp1 Hrm1_b"; last first.
    { iIntros "!>".
      wp_apply (resource_manager_spec rm1_addr with "[$] [$] [] [$] [$]");
        [set_solver| |done].
      iApply (big_sepS_elem_of with "Hrms_si"); set_solver. }
    iModIntro; wp_seq.
    wp_apply aneris_wp_start; iFrame.
    iSplitR "Hw2 Hp2 Hrm2_b"; last first.
    { iIntros "!>".
      wp_apply (resource_manager_spec rm2_addr with "[$] [$] [] [$] [$] ");
        [set_solver| |done].
      iApply (big_sepS_elem_of with "Hrms_si"); set_solver. }
    iModIntro; wp_seq.
    wp_apply aneris_wp_start; iFrame.
    iSplitR "Hw3 Hp3 Hrm3_b"; last first.
    { iIntros "!>".
      wp_apply (resource_manager_spec rm3_addr with "[$] [$] [] [$] [$] ");
        [set_solver| |done].
      iApply (big_sepS_elem_of with "Hrms_si"); set_solver. }
    iModIntro; wp_seq.
    wp_apply aneris_wp_start; iFrame.
    iSplitL "HΦ"; [by iApply "HΦ"|].
    iIntros "!>".
    wp_apply aneris_wp_wand_r; iSplitL.
    { wp_apply (transaction_manager_spec
                  with "[$] [$] [$] [$] [$]").
      by rewrite !union_assoc_L union_empty_r_L in H2. }
    by iIntros (?) "?".
  Qed.

End runner.
