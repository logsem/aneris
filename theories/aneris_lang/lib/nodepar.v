From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From aneris.aneris_lang Require Export lang tactics proofmode.
Set Default Proof Using "Type".

Notation "( ip1 ; e1 )  ||| ( ip2 ; e2 )" :=
  (Start ip2 e2, Start ip1 e1)%E.

Section proof.
  Context `{dG : !anerisG Mdl Σ}.

  Lemma par_spec Φ1 Φ2 P1 P2 ip1 ip2 e1 e2 :
    P1 ≠ ∅ ∧ P2 ≠ ∅ →
    ip1 ≠ "system" ∧ ip2 ≠ "system" →
    Φ1 ∗ Φ2 ∗
    free_ip ip1 ∗ free_ip ip2 ∗
    ((Φ1 -∗ free_ports ip1 P1 -∗ WP e1 @[ip1] {{ _, True }}) ∗
     (Φ2 -∗ free_ports ip2 P2 -∗ WP e2 @[ip2] {{ _, True }}))%I ⊢
    WP ((ip1; e1) ||| (ip2; e2)) @["system"] {{ _, True }}.
  Proof.
    iIntros ([HP1 HP2] [Hn1 Hn2]) "(HΦ1 & HΦ2 & HIP1 & HIP2 & Hwp1 & Hwp2)".
    wp_apply (aneris_wp_start P1 with "[-]"); [done|]. iFrame.
    iSplitR "HΦ1 Hwp1"; last first.
    { iNext. iIntros "Hp". iApply ("Hwp1" with "HΦ1 Hp"). }
    iNext. simpl.
    wp_apply (aneris_wp_start with "[-]"); [done|]. iFrame.
    iSplitR "HΦ2 Hwp2"; last first.
    { iNext. iIntros "Hp". iApply ("Hwp2" with "HΦ2 Hp"). }
    iNext. by wp_pures.
  Qed.

End proof.
