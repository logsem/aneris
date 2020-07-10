From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From aneris Require Export lang lifting network notation tactics proofmode.
Set Default Proof Using "Type".

Notation "( n1 ; ip1 ; e1 ) ||| ( n2 ; ip2 ; e2 )" :=
  (Start n2 ip2 e2, Start n1 ip1 e1)%E.

Section proof.
  Context `{ppd : !pingpongG Σ}
          `{dG : !distG Σ}.

  Lemma par_spec Φ1 Φ2 P1 P2 n1 n2 ip1 ip2 e1 e2 :
    n1 ≠ "system" ∧ n2 ≠ "system" →
    Φ1 ∗ Φ2 ∗
    FreeIP ip1 ∗ FreeIP ip2 ∗
    ((IsNode n1 -∗ Φ1 -∗ FreePorts ip1 P1 -∗ WP ⟨n1;e1⟩ {{ _, True }}) ∗
     (isNode n2 -∗ Φ2 -∗ FreePorts ip2 P2 -∗ WP ⟨n2;e2⟩ {{ _, True }}))%I ⊢
    WP ⟨"system"; (n1; ip1; e1) ||| (n2; ip2; e2)⟩ {{ _, True }}.
  Proof.
    iIntros ([Hn1 Hn2]) "(HΦ1 & HΦ2 & HIP1 & HIP2 & Hwp1 & Hwp2)".
    wp_apply (wp_start with "[-]"); first auto. iFrame.
    iSplitR "HΦ1 Hwp1"; last first.
    { iNext. iIntros "Hn Hp". iApply ("Hwp1" with "Hn HΦ1 Hp"). }
    iNext. simpl.
    wp_apply (wp_start with "[-]"); first auto. iFrame.
    iSplitR "HΦ2 Hwp2"; last first.
    { iNext. iIntros "Hn Hp". iApply ("Hwp2" with "Hn HΦ2 Hp"). }
    iNext. simpl. by wp_pures.
  Qed.

End proof.
