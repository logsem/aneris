From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import
     lang network tactics proofmode lifting adequacy.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb.spec Require Import spec.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb Require Import spec_util.
From aneris.examples.ccddb.examples Require Import lib.
From aneris.examples.ccddb.examples.message_passing Require Import prog.
From aneris.examples.ccddb.examples.message_passing Require Import
     proof_resources proof_of_node0 proof_of_node1.


Section ProofOfMain.
  Context `{!anerisG Mdl Σ, !mpG Σ}.
  Context `{!DB_time, !DB_events, !Maximals_Computing}.
  Context `{DB_init_function, !DB_init}.

  Definition ips : gset string := {[ "0.0.0.0" ; "0.0.0.1"]}.

  Theorem main_spec (A : gset socket_address) :
     z0 ∈ A -> z1 ∈ A ->
     ⊢ |={⊤}=> ∃ (_ : DB_resources Mdl Σ),
    ([∗ list] z ∈ DB_addresses, z ⤇ DB_socket_proto) -∗
    z0 ⤳ (∅, ∅) -∗
    z1 ⤳ (∅, ∅) -∗
    fixed A -∗ ([∗ set] ip ∈ ips, free_ip ip) -∗
    WP main @["system"] {{ v, True }}.
  Proof.
    iIntros (Hz0 Hz1) "".
    iMod (DB_init_setup $! (I: True))
        as (DBres) "(#GlobInv & (Hitk0 & Hitk1 & _) & Hkeys & #HinitSpec)".
    iModIntro.
    iExists _.
    iIntros "#Hproto Hrs0 Hrs1 #Hfix Hips".
    iDestruct (big_sepS_delete _ _ "0.0.0.0" with "Hips") as "(Hz0 & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "0.0.0.1" with "Hips") as "(Hz1 & _)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "x" with "Hkeys") as "(Hx & Hkeys)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "y" with "Hkeys") as "(Hy & _)";
      first set_solver.
    iMod (own_alloc (Excl ())) as (γ) "Htk"; first done.
    iApply fupd_aneris_wp.
    iMod (inv_alloc Ny _ (inv_y γ) with "[Hy]") as "#Hinvy".
    { iNext. iExists _; iFrame.
      iIntros (? [? ?]); set_solver. }
    iModIntro.
    rewrite /main.
    wp_apply (aneris_wp_start with "[-]"); first done.
    iFrame.
    iSplitR "Hitk0 Hx Hrs0"; last first.
    - iNext. iIntros "Hn".
      iApply fupd_aneris_wp.
      iModIntro. simpl.
      iApply (z0_node_spec with "[] [] [$Hn $Hitk0 $Hx $Hrs0]"); simpl;
        [done|done|done|iFrame "#"|done].
    - iNext. wp_seq.
      wp_apply (aneris_wp_start with "[-]"); first done.
      iFrame.
      iSplitR; first done.
      iNext. iIntros "Hn".
      iApply (z1_node_spec with "[] [] [$Hn $Hitk1 $Htk $Hrs1]"); simpl;
        [done|done|done|iFrame "#"|done].
  Qed.

End ProofOfMain.
