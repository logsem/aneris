From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params resources specs.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.snapshot_isolation.examples.no_serializability
      Require Import no_serializability_code.
Import ser_inj.
Import network_util_proof.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.
From aneris.examples.snapshot_isolation.util Require Import util_proof.

Definition server_addr := SocketAddressInet "0.0.0.0" 80.
Definition client_1_addr := SocketAddressInet "0.0.0.1" 80.
Definition client_2_addr := SocketAddressInet "0.0.0.2" 80.
Definition client_3_addr := SocketAddressInet "0.0.0.3" 80.
Definition client_4_addr := SocketAddressInet "0.0.0.4" 80.

Instance params : User_params :=
{| KVS_address := server_addr;
  KVS_keys := {["x"; "y"; "z"]};
  KVS_InvName := nroot .@ "siinv";
  KVS_serialization := int_serialization;
  KVS_ser_inj := int_ser_is_ser_injective;
  KVS_ser_inj_alt := int_ser_is_ser_injective_alt
|}.

Definition client_inv_name := nroot.@"clinv".

Section proofs.

Context `{!anerisG Mdl Σ, !SI_resources Mdl Σ, !SI_client_toolbox}.

  Definition client_inv_def : iProp Σ :=
  ∃ hx hy hz, "x" ↦ₖ hx ∗ "y" ↦ₖ hy ∗ "z" ↦ₖ hz ∗
      (⌜hz = []⌝ ∨
      (∃ vx vy, ⌜hist_val hx = Some vx⌝ ∗ ⌜hist_val hy = Some vy⌝ ∗
      (⌜vx = #1⌝ ∨ ⌜vx = #(-1)⌝) ∗(⌜vy = #1⌝ ∨ ⌜vy = #(-1)⌝))).

  Definition client_inv : iProp Σ :=
    inv client_inv_name client_inv_def.

  Lemma transaction1_spec :
    ∀ cst sa,
    client_inv -∗
    {{{ ConnectionState cst CanStart ∗ IsConnected cst }}}
      transaction1 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ !>(CanStart & #HiC) HΦ".
    rewrite/transaction1.
    wp_pures.
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name));
      first solve_ndisj.
    iInv "inv" as ">(%hx & %hy & %hz & x_hx & y_hy & z_hz & init)" "close".
    iModIntro.
    iExists {[ "x" := hx; "y" := hy; "z" := hz ]}.
    iFrame.
    iSplitL "x_hx y_hy z_hz";
      first by repeat (iApply big_sepM_insert; first done; iFrame).
    iIntros "!>(Active & mem & cache & _)".
    iMod ("close" with "[mem init]") as "_".
    {
      iNext.
      iExists hx, hy, hz.
      repeat (iPoseProof (big_sepM_insert with "mem") as "(k_hk & mem)";
                first done; iFrame).
    }
    iModIntro.
    wp_pures.
    iPoseProof (big_sepM_insert with "cache") as "((x_hx & x_upd) & cache)";
      first done.
    iPoseProof (big_sepM_insert with "cache") as "((y_hy & y_upd) & cache)";
      first done.
    iPoseProof (big_sepM_insert with "cache") as "((z_hz & z_upd) & _)";
      first done.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #1) with "[] [$x_hx $x_upd $HiC]");
      first set_solver.
    iIntros "(x_1 & x_upd)".
    wp_pures.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #1) with "[] [$y_hy $y_upd $HiC]");
      first set_solver.
    iIntros "(y_1 & y_upd)".
    wp_pures.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #1) with "[] [$z_hz $z_upd $HiC]");
      first set_solver.
    iIntros "(z_1 & z_upd)".
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' & #init)" "close".
    iModIntro.
    iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}, _,
      {[ "x" := (Some #1, true); "y" := (Some #1, true); "z" := (Some #1, true) ]}.
    iFrame.
    iSplitL "x_1 y_1 z_1 x_hx' y_hy' z_hz' x_upd y_upd z_upd".
    {
      rewrite !dom_insert_L !dom_empty_L.
      do 2 (iSplit; first done).
      by iSplitL "x_hx' y_hy' z_hz'";
        repeat (iApply big_sepM_insert; first done; iFrame).
    }
    have x_key : "x" ∈ KVS_keys by set_solver.
    have y_key : "y" ∈ KVS_keys by set_solver.
    have z_key : "z" ∈ KVS_keys by set_solver.
    iIntros "!>(CanStart & [(%can_commit & mem)|(_ & mem)])";
      (iMod ("close" with "[mem]") as "_"; last by iApply "HΦ").
    {
      iPoseProof (big_sepM2_insert with "mem") as "((x_1 & _) & mem)"; [done..|].
      iPoseProof (big_sepM2_insert with "mem") as "((y_1 & _) & mem)"; [done..|].
      iPoseProof (big_sepM2_insert with "mem") as "((z_1 & _) & _)"; [done..|].
      rewrite bool_decide_spec in can_commit.
      move: (can_commit _ x_key).
      rewrite lookup_insert bool_decide_spec !lookup_insert=>[][->].
      move: (can_commit _ y_key).
      rewrite lookup_insert_ne// lookup_insert bool_decide_spec lookup_insert_ne//
          lookup_insert lookup_insert_ne// lookup_insert=>[][->].
      move: (can_commit _ z_key).
      rewrite lookup_insert_ne// lookup_insert_ne// lookup_insert bool_decide_spec
            lookup_insert_ne// lookup_insert_ne// lookup_insert
            lookup_insert_ne// lookup_insert_ne// lookup_insert=>[][->].
      iNext.
      iExists (#1 :: hx), (#1 :: hy), (#1 :: hz).
      iFrame.
      iPureIntro.
      right.
      exists #1, #1.
      do 2 (split; first done).
      by split; left.
    }
    iPoseProof (big_sepM_insert with "mem") as "((x_hx' & _) & mem)"; first done.
    iPoseProof (big_sepM_insert with "mem") as "((y_hy' & _) & mem)"; first done.
    iPoseProof (big_sepM_insert with "mem") as "((z_hz' & _) & _)"; first done.
    iNext.
    iExists hx', hy', hz'.
    iFrame "∗#".
  Qed.

  Lemma transaction2_spec :
    ∀ cst sa,
    client_inv -∗
    {{{ ConnectionState cst CanStart ∗ IsConnected cst }}}
      transaction2 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ !>(CanStart & #HiC) HΦ".
    rewrite/transaction2.
    wp_pures.
    wp_apply (simple_wait_transaction_spec _ _ _ _ _  (⊤ ∖ ↑client_inv_name)
      with "[] [] [] [] [$CanStart $HiC]"); [solve_ndisj|set_solver|..].
    {
      iModIntro.
      iInv "inv" as ">(%hx & %hy & %hz & x_hx & y_hy & z_hz & %Hinv)" "close".
      iModIntro.
      iExists hz.
      iFrame.
      iIntros "!>z_hz".
      iMod ("close" with "[x_hx y_hy z_hz]") as "_"; last done.
      iNext.
      iExists hx, hy, hz.
      by iFrame.
    }
    {
      iIntros (v' Ψ) "!>_ HΨ".
      wp_pures.
      wp_op; first apply bin_op_eval_eq_val.
      iApply "HΨ".
      by rewrite bool_decide_spec.
    }
    iIntros (h) "(CanStart & #Seen)".
    wp_pures.
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx & %hy & %hz & x_hx & y_hy & z_hz &
      [->|(%vx & %vy & %hx_vx & %hy_vy & %Hvx & %Hvy)])" "close".
    {
      iMod (Seen_valid $! SI_GlobalInv with "[$Seen $z_hz]") as
          "(z_hz & %abs)"; first solve_ndisj.
      by apply suffix_nil_inv in abs.
    }
    iModIntro.
    iExists {[ "x" := hx; "y" := hy ]}.
    iFrame.
    iSplitL "x_hx y_hy";
      first by repeat (iApply big_sepM_insert; first done; iFrame).
    iIntros "!>(Active & mem & cache & _)".
    iMod ("close" with "[mem z_hz]") as "_".
    {
      iNext.
      iExists hx, hy, hz.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy & mem)"; first done.
      iFrame.
      iRight.
      by iExists vx, vy.
    }
    iModIntro.
    wp_pures.
    iPoseProof (big_sepM_delete _ _ "x" hx with "cache") as
        "((x_hx & x_upd) & cache)"; first done.
    iPoseProof (big_sepM_delete _ _ "y" hy with "cache") as
        "((y_hy & y_upd) & cache)"; first by rewrite lookup_delete_ne.
    wp_apply (SI_read_spec with "[] [ $HiC $x_hx]"); first set_solver.
    iIntros "x_hx".
    rewrite hx_vx hy_vy.
    destruct Hvx as [-> | ->].
    all: wp_pures.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #(-1)) with
        "[] [$y_hy $y_upd  $HiC]"); first set_solver.
    iIntros "(y_hy & y_upd)".
    wp_pures.
    all: wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    all: iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
      [->|(%vx' & %vy' & %hx'_vx' & %hy'_vy' & %Hvx' & %Hvy')])" "close".
    1, 3: iMod (Seen_valid $! SI_GlobalInv with "[$Seen $z_hz']") as
            "(z_hz' & %abs)"; first solve_ndisj.
    1, 2: by apply suffix_nil_inv in abs.
    all: iModIntro.
    all: iExists {[ "x" := hx'; "y" := hy' ]}, _.
    iExists {[ "x" := (Some #1, false); "y" := (Some #(-1), true) ]}.
    2: iExists {[ "x" := (Some #(-1), false); "y" := (Some vy, false) ]}.
    all: iFrame.
    all: rewrite !dom_insert_L !dom_empty_L.
    all: iSplitL "x_hx x_upd x_hx' y_hy y_upd y_hy'".
    1, 3: do 2 (iSplit; first set_solver).
    1, 2: by iSplitL "x_hx' y_hy'";
            repeat (iApply big_sepM_insert; first done; iFrame).
    all: iIntros "!>(CanStart & [(_ & kvs)|(_ & kvs)])".
    1, 3: iPoseProof (big_sepM2_insert with "kvs") as "((x_hx' & _) & kvs)";
          [done..|].
    1, 2: iPoseProof (big_sepM2_insert with "kvs") as "((y_hy' & _) & _)";
          [done..|].
    3, 4: iPoseProof (big_sepM_insert with "kvs") as "((x_hx' & _) & kvs)";
          first done.
    3, 4: iPoseProof (big_sepM_insert with "kvs") as "((y_hy' & _) & _)";
          first done.
    all: iMod ("close" with "[x_hx' y_hy' z_hz']") as "_";
          last iApply ("HΦ" with "[//]").
    all: iModIntro.
    iExists hx', (#(-1) :: hy'), hz'.
    2, 3, 4: iExists hx', hy', hz'.
    all: iFrame.
    all: iRight.
    2, 3, 4: by iExists _, _.
    iExists vx', #(-1).
    do 3 (iSplit; first done).
    by iRight.
  Qed.

  Lemma transaction3_spec :
    ∀ cst sa,
    client_inv -∗
    {{{ ConnectionState cst CanStart ∗ IsConnected cst }}}
      transaction3 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ!>(CanStart & #HiC) HΦ".
    rewrite/transaction3.
    wp_pures.
    wp_apply (simple_wait_transaction_spec _ _ _ _ _ (⊤ ∖ ↑client_inv_name)
      with "[] [] [] [] [$CanStart $HiC]"); [solve_ndisj|set_solver|..].
    {
      iModIntro.
      iInv "inv" as ">(%hx & %hy & %hz & x_hx & y_hy & z_hz & %Hinv)" "close".
      iModIntro.
      iExists hz.
      iFrame.
      iIntros "!>z_hz".
      iMod ("close" with "[x_hx y_hy z_hz]") as "_"; last done.
      iNext.
      iExists hx, hy, hz.
      by iFrame.
    }
    {
      iIntros (v' Ψ) "!>_ HΨ".
      wp_pures.
      wp_op; first apply bin_op_eval_eq_val.
      iApply "HΨ".
      by rewrite bool_decide_spec.
    }
    iIntros (h) "(CanStart & #Seen)".
    wp_pures.
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx & %hy & %hz & x_hx & y_hy & z_hz &
      [->|(%vx & %vy & %hx_vx & %hy_vy & %Hvx & %Hvy)])" "close".
    {
      iMod (Seen_valid $! SI_GlobalInv with "[$Seen $z_hz]") as
          "(z_hz & %abs)"; first solve_ndisj.
      by apply suffix_nil_inv in abs.
    }
    iModIntro.
    iExists {[ "x" := hx; "y" := hy ]}.
    iFrame.
    iSplitL "x_hx y_hy";
      first by repeat (iApply big_sepM_insert; first done; iFrame).
    iIntros "!>(Active & mem & cache & _)".
    iMod ("close" with "[mem z_hz]") as "_".
    {
      iNext.
      iExists hx, hy, hz.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy & mem)"; first done.
      iFrame.
      iRight.
      by iExists vx, vy.
    }
    iModIntro.
    wp_pures.
    iPoseProof (big_sepM_delete _ _ "x" hx with "cache") as
        "((x_hx & x_upd) & cache)"; first done.
    iPoseProof (big_sepM_delete _ _ "y" hy with "cache") as
        "((y_hy & y_upd) & _)"; first by rewrite lookup_delete_ne.
    wp_apply (SI_read_spec with "[] [$y_hy $HiC]"); first set_solver.
    iIntros "y_hy".
    rewrite hx_vx hy_vy.
    destruct Hvy as [-> | ->].
    all: wp_pures.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #(-1)) with
        "[] [$x_hx $x_upd $HiC]"); first set_solver.
    iIntros "(x_hx & x_upd)".
    wp_pures.
    all: wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    all: iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
      [->|(%vx' & %vy' & %hx'_vx' & %hy'_vy' & %Hvx' & %Hvy')])" "close".
    1, 3: iMod (Seen_valid $! SI_GlobalInv with "[$Seen $z_hz']") as
            "(z_hz' & %abs)"; first solve_ndisj.
    1, 2: by apply suffix_nil_inv in abs.
    all: iModIntro.
    all: iExists {[ "x" := hx'; "y" := hy' ]}, _.
    iExists {[ "x" := (Some #(-1), true); "y" := (Some #1, false) ]}.
    2: iExists {[ "x" := (Some vx, false); "y" := (Some #(-1), false) ]}.
    all: iFrame.
    all: rewrite !dom_insert_L !dom_empty_L.
    all: iSplitL "x_hx x_upd x_hx' y_hy y_upd y_hy'".
    1, 3: do 2 (iSplit; first set_solver).
    1, 2: by iSplitL "x_hx' y_hy'";
            repeat (iApply big_sepM_insert; first done; iFrame).
    all: iIntros "!>(CanStart & [(_ & kvs)|(_ & kvs)])".
    1, 3: iPoseProof (big_sepM2_insert with "kvs") as "((x_hx' & _) & kvs)";
          [done..|].
    1, 2: iPoseProof (big_sepM2_insert with "kvs") as "((y_hy' & _) & _)";
          [done..|].
    3, 4: iPoseProof (big_sepM_insert with "kvs") as "((x_hx' & _) & kvs)";
          first done.
    3, 4: iPoseProof (big_sepM_insert with "kvs") as "((y_hy' & _) & _)";
          first done.
    all: iMod ("close" with "[x_hx' y_hy' z_hz']") as "_";
          last iApply ("HΦ" with "[//]").
    all: iModIntro.
    iExists (#(-1) :: hx'), hy', hz'.
    2, 3, 4: iExists hx', hy', hz'.
    all: iFrame.
    all: iRight.
    2, 3, 4: by iExists _, _.
    iExists #(-1), vy'.
    do 2 (iSplit; first done).
    by iSplit; first iRight.
  Qed.

  Lemma transaction4_spec :
    ∀ cst sa,
    client_inv -∗
    {{{ ConnectionState cst CanStart ∗ IsConnected cst }}}
      transaction4 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ !>(CanStart & #HiC) HΦ".
    rewrite/transaction4.
    wp_pures.
    wp_apply (simple_wait_transaction_spec _ _ _ _ _ (⊤ ∖ ↑client_inv_name)
      with "[] [] [] [] [$CanStart $HiC]"); [solve_ndisj|set_solver|..].
    {
      iModIntro.
      iInv "inv" as ">(%hx & %hy & %hz & x_hx & y_hy & z_hz & %Hinv)" "close".
      iModIntro.
      iExists hz.
      iFrame.
      iIntros "!>z_hz".
      iMod ("close" with "[x_hx y_hy z_hz]") as "_"; last done.
      iNext.
      iExists hx, hy, hz.
      by iFrame.
    }
    {
      iIntros (v' Ψ) "!>_ HΨ".
      wp_pures.
      wp_op; first apply bin_op_eval_eq_val.
      iApply "HΨ".
      by rewrite bool_decide_spec.
    }
    iIntros (h) "(CanStart & #Seen)".
    wp_pures.
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx & %hy & %hz & x_hx & y_hy & z_hz &
      [->|(%vx & %vy & %hx_vx & %hy_vy & %Hvx & %Hvy)])" "close".
    {
      iMod (Seen_valid $! SI_GlobalInv with "[$Seen $z_hz]") as
          "(z_hz & %abs)"; first solve_ndisj.
      by apply suffix_nil_inv in abs.
    }
    iModIntro.
    iExists {[ "x" := hx; "y" := hy ]}.
    iFrame.
    iSplitL "x_hx y_hy";
      first by repeat (iApply big_sepM_insert; first done; iFrame).
    iIntros "!>(Active & mem & cache & _)".
    iMod ("close" with "[mem z_hz]") as "_".
    {
      iNext.
      iExists hx, hy, hz.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy & mem)"; first done.
      iFrame.
      iRight.
      by iExists vx, vy.
    }
    iModIntro.
    wp_pures.
    iPoseProof (big_sepM_delete _ _ "x" hx with "cache") as
        "((x_hx & x_upd) & cache)"; first done.
    iPoseProof (big_sepM_delete _ _ "y" hy with "cache") as
        "((y_hy & y_upd) & _)"; first by rewrite lookup_delete_ne.
    wp_apply (SI_read_spec with "[]  [$x_hx $HiC]"); first set_solver.
    iIntros "x_hx".
    rewrite hx_vx hy_vy/unSOME /assert.
    wp_pures.
    wp_apply (SI_read_spec with "[] [$y_hy $HiC]"); first set_solver.
    iIntros "y_hy".
    wp_pures.
    move: Hvx Hvy hx_vx hy_vy=>[]->[]->hx_vx hy_vy.
    all: wp_pures.
    all: wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    all: iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' & %Hinv)"
                          "close".
    all: iModIntro.
    all: iExists {[ "x" := hx'; "y" := hy' ]}, _,
            {[ "x" := (_, false); "y" := (_, false) ]}.
    all: iFrame.
    all: rewrite !dom_insert_L !dom_empty_L.
    all: iSplitL "x_upd x_hx x_hx' y_upd y_hy y_hy'".
    1, 3, 5, 7: do 2 (iSplit; first done).
    1, 2, 3, 4: by iSplitL "x_hx' y_hy'";
                  repeat (iApply big_sepM_insert; first done; iFrame).
    all: iIntros "!>(_ & [(_ & kvs)|(_ & kvs)])".
    1, 3, 5, 7: iPoseProof (big_sepM2_insert with "kvs") as "((x_hx' & _) & kvs)";
        [done..|].
    1, 2, 3, 4: iPoseProof (big_sepM2_insert with "kvs") as "((y_hy' & _) & _)";
        [done..|].
    5, 6, 7, 8: iPoseProof (big_sepM_insert with "kvs") as "((x_hx' & _) & kvs)";
        first done.
    5, 6, 7, 8: iPoseProof (big_sepM_insert with "kvs") as "((y_hy' & _) & _)";
        first done.
    all: iMod ("close" with "[x_hx' y_hy' z_hz']") as "_";
          last iApply ("HΦ" with "[//]").
    all: iNext.
    all: iExists hx', hy', hz'.
    all: by iFrame.
  Qed.

  Lemma transaction1_client_spec :
    ∀ sa,
    client_inv -∗
    {{{
      sa ⤳ (∅, ∅) ∗
      unallocated {[sa]} ∗
      KVS_ClientCanConnect sa ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      KVS_address ⤇ KVS_si
    }}}
      transaction1_client $sa $KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (sa) "#inv %Φ !>(∅ & unalloc & free & Hcc & #KVS_si) HΦ".
    rewrite/transaction1_client.
    wp_pures.
    wp_apply (SI_init_client_proxy_spec with "[$]").
    iIntros (cst) "CanStart".
    wp_pures.
    by wp_apply (transaction1_spec with "inv [$]").
  Qed.

  Lemma transaction2_client_spec :
    ∀ sa,
    client_inv -∗
    {{{
      sa ⤳ (∅, ∅) ∗
      unallocated {[sa]} ∗
      KVS_ClientCanConnect sa ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      KVS_address ⤇ KVS_si
    }}}
      transaction2_client $sa $KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (sa) "#inv %Φ !>(∅ & unalloc & free & Hcc & #KVS_si) HΦ".
    rewrite/transaction2_client.
    wp_pures.
    wp_apply (SI_init_client_proxy_spec with "[$]").
    iIntros (cst) "CanStart".
    wp_pures.
    by wp_apply (transaction2_spec with "inv [$]").
  Qed.

  Lemma transaction3_client_spec :
    ∀ sa,
    client_inv -∗
    {{{
      sa ⤳ (∅, ∅) ∗
      unallocated {[sa]} ∗
      KVS_ClientCanConnect sa ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      KVS_address ⤇ KVS_si
    }}}
      transaction3_client $sa $KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (sa) "#inv %Φ !>(∅ & unalloc & free & Hcc & #KVS_si) HΦ".
    rewrite/transaction3_client.
    wp_pures.
    wp_apply (SI_init_client_proxy_spec with "[$]").
    iIntros (cst) "CanStart".
    wp_pures.
    by wp_apply (transaction3_spec with "inv [$]").
  Qed.

  Lemma transaction4_client_spec :
    ∀ sa,
    client_inv -∗
    {{{
      sa ⤳ (∅, ∅) ∗
      unallocated {[sa]} ∗
      KVS_ClientCanConnect sa ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      KVS_address ⤇ KVS_si
    }}}
      transaction4_client $sa $KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (sa) "#inv %Φ !>(∅ & unalloc & Hcc & free & #KVS_si) HΦ".
    rewrite/transaction4_client.
    wp_pures.
    wp_apply (SI_init_client_proxy_spec with "[$]").
    iIntros (cst) "CanStart".
    wp_pures.
    by wp_apply (transaction4_spec with "inv [$]").
  Qed.

  Lemma server_spec :
    {{{ KVS_Init
      ∗ KVS_address ⤳ (∅, ∅)
      ∗ free_ports (ip_of_address KVS_address) {[port_of_address KVS_address]}
      ∗ KVS_address ⤇ KVS_si }}}
    server #KVS_address @[ip_of_address KVS_address]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(? & ? & ? & ?) HΦ".
    rewrite /server. wp_pures.
    by wp_apply (SI_init_kvs_spec with "[$]").
  Qed.

End proofs.

Section proof_runner.

Context `{!anerisG Mdl Σ, !SI_init, !KVSG Σ}.

  Definition example_runner : expr :=
    let: "serveraddr" := MakeAddress #"0.0.0.0" #80 in
    let: "client1addr" := MakeAddress #"0.0.0.1" #80 in
    let: "client2addr" := MakeAddress #"0.0.0.2" #80 in
    let: "client3addr" := MakeAddress #"0.0.0.3" #80 in
    let: "client4addr" := MakeAddress #"0.0.0.4" #80 in
    Start "0.0.0.0" (server "serveraddr") ;;
    Start "0.0.0.1" (transaction1_client "client1addr" "serveraddr") ;;
    Start "0.0.0.2" (transaction2_client "client2addr" "serveraddr") ;;
    Start "0.0.0.3" (transaction3_client "client3addr" "serveraddr") ;;
    Start "0.0.0.4" (transaction4_client "client4addr" "serveraddr").

  Lemma example_runner_spec :
    {{{ server_addr ⤳ (∅, ∅)
      ∗ client_1_addr ⤳ (∅, ∅)
      ∗ client_2_addr ⤳ (∅, ∅)
      ∗ client_3_addr ⤳ (∅, ∅)
      ∗ client_4_addr ⤳ (∅, ∅)
      ∗ unallocated {[server_addr]}
      ∗ unallocated {[client_1_addr]}
      ∗ unallocated {[client_2_addr]}
      ∗ unallocated {[client_3_addr]}
      ∗ unallocated {[client_4_addr]}
      ∗ free_ip (ip_of_address server_addr)
      ∗ free_ip (ip_of_address client_1_addr)
      ∗ free_ip (ip_of_address client_2_addr)
      ∗ free_ip (ip_of_address client_3_addr)
      ∗ free_ip (ip_of_address client_4_addr)
     }}}
      example_runner @["system"]
    {{{ RET #(); True }}}.
  Proof.
    iMod (SI_init_module 
            _ 
            {[client_1_addr; client_2_addr;
              client_3_addr; client_4_addr]}) 
      as (SI_res SI_client_toolbox) "(mem & KVS_Init & Hcc)".
    iPoseProof (big_sepS_delete _ _ "x" with "mem") as "(mem_x & mem)";
      first done.
    iPoseProof (big_sepS_delete _ _ "y" with "mem") as "(mem_y & mem)";
      first done.
    iPoseProof (big_sepS_delete _ _ "z" with "mem") as "(mem_z & _)";
      first done.
    iMod (inv_alloc client_inv_name _ client_inv_def with "[mem_x mem_y mem_z]")
      as "#inv".
    { iNext. iExists _, _, _. iFrame. by iLeft. }
    iIntros (Φ) "(srv_∅ & clt1_∅ & clt2_∅ & clt3_∅ & clt4_∅ & srv_unalloc &
      clt1_unalloc & clt2_unalloc & clt3_unalloc & clt4_unalloc &
      ? & ? & ? & ? & ?) HΦ".
    rewrite /example_runner.
    wp_pures.
    wp_apply (aneris_wp_socket_interp_alloc_singleton KVS_si with "srv_unalloc").
    iIntros "#KVS_si".
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "srv_∅ KVS_Init"; last first.
    {
      iIntros "!>Hports".
      by wp_apply (server_spec with "[$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iDestruct (big_sepS_delete _  _ client_1_addr with "Hcc")
      as "(Hcc1 & Hcc)";
      first set_solver.
    iDestruct (big_sepS_delete _  _ client_2_addr with "Hcc")
      as "(Hcc2 & Hcc)";
      first set_solver.
    iDestruct (big_sepS_delete _  _ client_3_addr with "Hcc")
      as "(Hcc3 & Hcc)";
      first set_solver.
    iDestruct (big_sepS_delete _  _ client_4_addr with "Hcc")
      as "(Hcc4 & Hcc)";
      first set_solver.
    iSplitR "clt1_∅ clt1_unalloc Hcc1"; last first.
    {
      iIntros "!>Hports".
      by wp_apply (transaction1_client_spec client_1_addr with "inv [$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "clt2_∅ clt2_unalloc Hcc2"; last first.
    {
      iIntros "!>Hports".
      by wp_apply (transaction2_client_spec client_2_addr with "inv [$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "clt3_∅ clt3_unalloc Hcc3"; last first.
    {
      iIntros "!>Hports".
      by wp_apply (transaction3_client_spec client_3_addr with "inv [$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "clt4_∅ clt4_unalloc Hcc4"; last first.
    {
      iIntros "!>Hports".
      by wp_apply (transaction4_client_spec client_4_addr with "inv [$]").
    }
    by iApply "HΦ".
  Qed.

End proof_runner.

Definition unit_model := model _ (λ _ _, False) ().
Lemma unit_model_rel_finitary : aneris_model_rel_finitary unit_model.
Proof. intros ?. apply finite_smaller_card_nat. apply _. Qed.

Definition ips : gset string :=
  {[ ip_of_address server_addr ; ip_of_address client_1_addr
  ; ip_of_address client_2_addr ; ip_of_address client_3_addr
  ; ip_of_address client_4_addr]}.

Definition sa_dom : gset socket_address :=
  {[ server_addr ; client_1_addr; client_2_addr; client_3_addr; client_4_addr ]}.

Definition init_state :=
  {|
    state_heaps := {["system" := ∅ ]};
    state_sockets := {["system" := ∅ ]};
    state_ms := ∅;
  |}.

Theorem runner_safe :
  aneris_adequate example_runner "system" init_state (λ _, True).
Proof.
  set (Σ := #[anerisΣ unit_model; KVSΣ]).
  apply (@adequacy Σ unit_model _ _ ips sa_dom ∅ ∅ ∅);
  [apply unit_model_rel_finitary | |set_solver..].
  iIntros (dinvG). iIntros "!> Hunallocated Hhist Hfrag Hips Hlbl _ _ _ _".
  iApply (example_runner_spec with "[Hunallocated Hhist Hfrag Hips Hlbl]" ).
  2 : { iModIntro. done. }
  do 4 (iDestruct (unallocated_split with "Hunallocated") as "[Hunallocated ?]";
  [set_solver|]). iFrame.
  do 4 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
  iDestruct "Hhist" as "[Hhist ?]"; iFrame).
  do 4 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
  iDestruct "Hips" as "[Hips ?]"; iFrame).
Qed.
