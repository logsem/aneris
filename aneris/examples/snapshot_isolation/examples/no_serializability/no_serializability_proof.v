(*From aneris.aneris_lang Require Import network resources proofmode.
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
    ((⌜hx = []⌝ ∗ ⌜hy = []⌝ ∗ ⌜hz = []⌝) ∨
      (⌜#1 ∈ hz⌝ ∗ ∃ vx vy, ⌜hist_val hx = Some vx⌝ ∗ ⌜hist_val hy = Some vy⌝ ∗
      (⌜vx = #1⌝ ∨ ⌜vx = #(-1)⌝) ∗(⌜vy = #1⌝ ∨ ⌜vy = #(-1)⌝))).

  Definition client_inv : iProp Σ :=
    inv client_inv_name client_inv_def.

  Lemma transaction1_spec :
    ∀ cst sa,
    client_inv -∗
    {{{ ConnectionState cst CanStart }}}
      transaction1 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ !>CanStart HΦ".
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
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #1) with "[] [$x_hx $x_upd]");
      first set_solver.
    iIntros "(x_1 & x_upd)".
    wp_pures.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #1) with "[] [$y_hy $y_upd]");
      first set_solver.
    iIntros "(y_1 & y_upd)".
    wp_pures.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #1) with "[] [$z_hz $z_upd]");
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
      split; first repeat constructor.
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
    {{{ ConnectionState cst CanStart }}}
      transaction2 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ!>CanStart HΦ".
    rewrite/transaction2.
    wp_pures.
    wp_apply (simple_wait_transaction_spec _ _ _ _ _ _ (⊤ ∖ ↑client_inv_name)
      with "[] [] [] [] [] CanStart").
    iIntros 
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx & %hy & %hz & x_hx & y_hy & z_hz & init)" "close".
    iModIntro.
    iExists {[ "x" := hx; "y" := hy; "z" := hz ]}.
    iFrame.
    iSplitL "x_hx y_hy z_hz";
      first by repeat (iApply big_sepM_insert; first done; iFrame).
    iIntros "!>(Active & mem & cache & Seen)".
    iMod ("close" with "[mem init]") as "_".
    {
      iNext.
      iExists hx, hy, hz.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(z_hz & _)"; first done.
      iFrame.
    }
    iModIntro.
    wp_pures.
    wp_apply (simplified_wait_on_keyT_spec _ _ #1 _ _ _ (⊤ ∖ ↑client_inv_name)
        (λ m, ∃ hx hy hz vx vy, ⌜m !! "x" = Some hx⌝ ∗ ⌜m !! "y" = Some hy⌝ ∗
          ⌜m !! "z" = Some hz⌝ ∗ ⌜#1 ∈ hz⌝ ∗
          ⌜hist_val hx = Some vx⌝ ∗ ⌜hist_val hy = Some vy⌝ ∗
          (⌜vx = #1⌝ ∨ ⌜vx = #(-1)⌝) ∗ (⌜vy = #1⌝ ∨ ⌜vy = #(-1)⌝))%I
          emp emp with
          "[] [] [] [] [] [] [$Active $cache $Seen]"); first solve_ndisj.
    1, 2 : rewrite !dom_insert_L; iPureIntro; set_solver.
    {
      iIntros "!>%h (#Seen & _)".
      iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
          [(_ & _ & ->)|(%hz'_1 & (%vx & %vy & %hx'_vx & %hy'_vy & 
            (%Hvx & %Hvy)))])" "close".
      { iMod (Seen_valid with "[] [$Seen $z_hz']") as "(z_hz' & %abs)";
          [solve_ndisj|iApply SI_GlobalInv|by apply suffix_nil_inv in abs].
      }
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}.
      iSplit; first by rewrite !dom_insert_L.
      iSplitL "x_hx' y_hy' z_hz'";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
      iSplitR.
      {
        iExists hx', hy', hz', vx, vy.
        iFrame "%".
        by rewrite (lookup_insert_ne _ _ "y").
      }
      iSplitR; first done.
      iIntros "!>(mem & _)".
      iMod ("close" with "[mem]") as "_"; last done.
      iNext.
      iExists hx', hy', hz'.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(z_hz' & _)"; first done.
      iFrame.
      iRight.
      iSplit; first done.
      by iExists vx, vy.
    }
    {
      iModIntro.
      iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
          %Hinv)" "close".
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}.
      iSplit; first by rewrite !dom_insert_L.
      iSplitL "x_hx' y_hy' z_hz'";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
      iIntros "!>mem".
      iMod ("close" with "[mem]") as "_"; last done.
      iNext.
      iExists hx', hy', hz'.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(z_hz' & _)"; first done.
      iFrame "∗ %".
    }
    {
      iIntros (v' Ψ) "!>_ HΨ".
      wp_pures.
      wp_op; first apply bin_op_eval_eq_val.
      iApply "HΨ".
      by rewrite bool_decide_spec.
    }
    rewrite !dom_insert_L.
    iClear (hx hy hz) "".
    iIntros (m) "(%dom_m & (%hx & %hy & %hz & %vx & %vy & %m_x & %m_y & %m_z &
          %hz_not_empty & %hx_vx & %hy_vy & %Hvx & %Hvy) & Active & cache & Seen)".
    wp_pures.
    iPoseProof (big_sepM_delete _ _ _ _ m_x with "cache") as
        "((x_hx & x_upd) & cache)".
    iPoseProof (big_sepM_delete _ _ "y" hy with "cache") as
        "((y_hy & y_upd) & cache)"; first by rewrite lookup_delete_ne.
    iPoseProof (big_sepM_delete _ _ "z" hz with "cache") as
        "((z_hz & z_upd) & _)"; first by rewrite !lookup_delete_ne.
    iPoseProof (big_sepM_lookup _ _ _ _ m_z with "Seen") as "#Seen_z".
    wp_apply (SI_read_spec with "[] x_hx"); first set_solver.
    iIntros "x_hx".
    rewrite hx_vx hy_vy.
    destruct Hvx as [-> | ->].
    {
      wp_pures.
      wp_apply (SI_write_spec $! _ _ _ _ (SerVal #(-1)) with
          "[] [$y_hy $y_upd]"); first set_solver.
      iIntros "(y_1 & y_upd)".
      wp_pures.
      wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
      iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
          [(_ & _ & ->)|(%hz'_not_empty & %vx' & %vy' & %hx'_vx' & 
            %hy'_vy' & %Hvx' & %Hvy')])" "close".
      {
        iMod (Seen_valid $! SI_GlobalInv with "[$Seen_z $z_hz']") as
            "(z_hz' & %abs)"; first solve_ndisj.
        apply suffix_nil_inv in abs.
        rewrite abs in hz_not_empty.
        by apply elem_of_nil in hz_not_empty.
      }
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}, m,
              {[ "x" := (Some #1, false); "y" := (Some #(-1), true);
                  "z" := (hist_val hz, false) ]}.
      iFrame.
      iSplitL "x_hx x_hx' x_upd y_1 y_hy' y_upd z_hz z_hz' z_upd".
      {
        rewrite !dom_insert_L dom_m !dom_empty_L.
        do 2 (iSplit; first done).
        by iSplitL "x_hx' y_hy' z_hz'";
            repeat (iApply big_sepM_insert; first done; iFrame).
      }
      iIntros "!>(_ & [(_ & mem)|(_ & mem)])".
      {
        iMod ("close" with "[mem]") as "_"; last by iApply "HΦ".
        iPoseProof (big_sepM2_insert with "mem") as "((x_hx' & _) & mem)";
          [done..|].
        iPoseProof (big_sepM2_insert with "mem") as "((y_hy' & _) & mem)";
          [done..|].
        iPoseProof (big_sepM2_insert with "mem") as "((z_hz' & _) & _)";
          [done..|].
        have -> : commit_event (hist_val hz, false) hz' = hz'
              by case: (hist_val hz).
        iNext.
        iExists hx', (#(-1) :: hy'), hz'.
        iFrame.
        iPureIntro.
        right.
        split; first done.
        exists vx', #(-1).
        do 2 (split; first done).
        by split; last right.
      }
      iMod ("close" with "[mem]") as "_"; last by iApply "HΦ".
      iPoseProof (big_sepM_insert with "mem") as "((x_hx' & _) & mem)";
          first done.
      iPoseProof (big_sepM_insert with "mem") as "((y_hy' & _) & mem)";
          first done.
      iPoseProof (big_sepM_insert with "mem") as "((z_hz' & _) & _)";
          first done.
      iNext.
      iExists _, _, _.
      iFrame.
      iPureIntro.
      right.
      split; first done.
      by exists vx', vy'.
    }
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
          %Hinv)" "close".
    iModIntro.
    iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}, m,
            {[ "x" := (Some #(-1), false); "y" := (Some vy, false);
                "z" := (hist_val hz, false) ]}.
    iFrame.
    iSplitL "x_upd x_hx x_hx' y_upd y_hy y_hy' z_upd z_hz z_hz'".
    {
      rewrite !dom_insert_L dom_m !dom_empty_L.
      do 2 (iSplit; first done).
      by iSplitL "x_hx' y_hy' z_hz'";
          repeat (iApply big_sepM_insert; first done; iFrame).
    }
    iIntros "!>(_ & [(_ & mem)|(_ & mem)])".
    {
      iMod ("close" with "[mem]") as "_"; last by iApply "HΦ".
      iPoseProof (big_sepM2_insert with "mem") as "((x_hx' & _) & mem)";
        [done..|].
      iPoseProof (big_sepM2_insert with "mem") as "((y_hy' & _) & mem)";
        [done..|].
      iPoseProof (big_sepM2_insert with "mem") as "((z_hz' & _) & _)";
        [done..|].
      have -> : commit_event (hist_val hz, false) hz' = hz'
            by case: (hist_val hz).
      iNext.
      iExists hx', hy', hz'.
      by iFrame.
    }
    iMod ("close" with "[mem]") as "_"; last by iApply "HΦ".
    iPoseProof (big_sepM_insert with "mem") as "((x_hx' & _) & mem)";
      [done..|].
    iPoseProof (big_sepM_insert with "mem") as "((y_hy' & _) & mem)";
      [done..|].
    iPoseProof (big_sepM_insert with "mem") as "((z_hz' & _) & _)";
      [done..|].
    iNext.
    iExists _, _, _.
    by iFrame.
  Qed.

  Lemma transaction3_spec :
    ∀ cst sa,
    client_inv -∗
    {{{ ConnectionState cst CanStart }}}
      transaction3 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ!>CanStart HΦ".
    rewrite/transaction3.
    wp_pures.
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx & %hy & %hz & x_hx & y_hy & z_hz & init)" "close".
    iModIntro.
    iExists {[ "x" := hx; "y" := hy; "z" := hz ]}.
    iFrame.
    iSplitL "x_hx y_hy z_hz";
      first by repeat (iApply big_sepM_insert; first done; iFrame).
    iIntros "!>(Active & mem & cache & Seen)".
    iMod ("close" with "[mem init]") as "_".
    {
      iNext.
      iExists hx, hy, hz.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(z_hz & _)"; first done.
      iFrame.
    }
    iModIntro.
    wp_pures.
    wp_apply (simplified_wait_on_keyT_spec _ _ #1 _ _ _ (⊤ ∖ ↑client_inv_name)
        (λ m, ∃ hx hy hz vx vy, ⌜m !! "x" = Some hx⌝ ∗ ⌜m !! "y" = Some hy⌝ ∗
          ⌜m !! "z" = Some hz⌝ ∗ ⌜#1 ∈ hz⌝ ∗
          ⌜hist_val hx = Some vx⌝ ∗ ⌜hist_val hy = Some vy⌝ ∗
          (⌜vx = #1⌝ ∨ ⌜vx = #(-1)⌝) ∗ (⌜vy = #1⌝ ∨ ⌜vy = #(-1)⌝))%I
          emp emp with
          "[] [] [] [] [] [] [$Active $cache $Seen]"); first solve_ndisj.
    1, 2 : rewrite !dom_insert_L; iPureIntro; set_solver.
    {
      iIntros "!>%h (#Seen & _)".
      iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
          [(_ & _ & ->)|(%hz'_1 & (%vx & %vy & %hx'_vx & %hy'_vy & 
            (%Hvx & %Hvy)))])" "close".
      { iMod (Seen_valid with "[] [$Seen $z_hz']") as "(z_hz' & %abs)";
          [solve_ndisj|iApply SI_GlobalInv|by apply suffix_nil_inv in abs].
      }
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}.
      iSplit; first by rewrite !dom_insert_L.
      iSplitL "x_hx' y_hy' z_hz'";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
      iSplitR.
      {
        iExists hx', hy', hz', vx, vy.
        iFrame "%".
        by rewrite (lookup_insert_ne _ _ "y").
      }
      iSplitR; first done.
      iIntros "!>(mem & _)".
      iMod ("close" with "[mem]") as "_"; last done.
      iNext.
      iExists hx', hy', hz'.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(z_hz' & _)"; first done.
      iFrame.
      iRight.
      iSplit; first done.
      by iExists vx, vy.
    }
    {
      iModIntro.
      iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
          %Hinv)" "close".
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}.
      iSplit; first by rewrite !dom_insert_L.
      iSplitL "x_hx' y_hy' z_hz'";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
      iIntros "!>mem".
      iMod ("close" with "[mem]") as "_"; last done.
      iNext.
      iExists hx', hy', hz'.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(z_hz' & _)"; first done.
      iFrame "∗ %".
    }
    {
      iIntros (v' Ψ) "!>_ HΨ".
      wp_pures.
      wp_op; first apply bin_op_eval_eq_val.
      iApply "HΨ".
      by rewrite bool_decide_spec.
    }
    rewrite !dom_insert_L.
    iClear (hx hy hz) "".
    iIntros (m) "(%dom_m & (%hx & %hy & %hz & %vx & %vy & %m_x & %m_y & %m_z &
          %hz_not_empty & %hx_vx & %hy_vy & %Hvx & %Hvy) & Active & cache & Seen)".
    wp_pures.
    iPoseProof (big_sepM_delete _ _ _ _ m_x with "cache") as
        "((x_hx & x_upd) & cache)".
    iPoseProof (big_sepM_delete _ _ "y" hy with "cache") as
        "((y_hy & y_upd) & cache)"; first by rewrite lookup_delete_ne.
    iPoseProof (big_sepM_delete _ _ "z" hz with "cache") as
        "((z_hz & z_upd) & _)"; first by rewrite !lookup_delete_ne.
    iPoseProof (big_sepM_lookup _ _ _ _ m_z with "Seen") as "#Seen_z".
    wp_apply (SI_read_spec with "[] y_hy"); first set_solver.
    iIntros "y_hy".
    rewrite hx_vx hy_vy.
    destruct Hvy as [-> | ->].
    {
      wp_pures.
      wp_apply (SI_write_spec $! _ _ _ _ (SerVal #(-1)) with
          "[] [$x_hx $x_upd]"); first set_solver.
      iIntros "(x_1 & x_upd)".
      wp_pures.
      wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
      iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
          [(_ & _ & ->)|(%hz'_not_empty & %vx' & %vy' & %hx'_vx' & 
            %hy'_vy' & %Hvx' & %Hvy')])" "close".
      {
        iMod (Seen_valid $! SI_GlobalInv with "[$Seen_z $z_hz']") as
            "(z_hz' & %abs)"; first solve_ndisj.
        apply suffix_nil_inv in abs.
        rewrite abs in hz_not_empty.
        by apply elem_of_nil in hz_not_empty.
      }
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}, m,
              {[ "x" := (Some #(-1), true); "y" := (Some #1, false);
                  "z" := (hist_val hz, false) ]}.
      iFrame.
      iSplitL "x_1 x_hx' x_upd y_hy y_hy' y_upd z_hz z_hz' z_upd".
      {
        rewrite !dom_insert_L dom_m !dom_empty_L.
        do 2 (iSplit; first done).
        by iSplitL "x_hx' y_hy' z_hz'";
            repeat (iApply big_sepM_insert; first done; iFrame).
      }
      iIntros "!>(_ & [(_ & mem)|(_ & mem)])".
      {
        iMod ("close" with "[mem]") as "_"; last by iApply "HΦ".
        iPoseProof (big_sepM2_insert with "mem") as "((x_hx' & _) & mem)";
          [done..|].
        iPoseProof (big_sepM2_insert with "mem") as "((y_hy' & _) & mem)";
          [done..|].
        iPoseProof (big_sepM2_insert with "mem") as "((z_hz' & _) & _)";
          [done..|].
        have -> : commit_event (hist_val hz, false) hz' = hz'
              by case: (hist_val hz).
        iNext.
        iExists (#(-1) :: hx'), hy', hz'.
        iFrame.
        iPureIntro.
        right.
        split; first done.
        exists #(-1), vy'.
        do 2 (split; first done).
        by split; first right.
      }
      iMod ("close" with "[mem]") as "_"; last by iApply "HΦ".
      iPoseProof (big_sepM_insert with "mem") as "((x_hx' & _) & mem)";
          first done.
      iPoseProof (big_sepM_insert with "mem") as "((y_hy' & _) & mem)";
          first done.
      iPoseProof (big_sepM_insert with "mem") as "((z_hz' & _) & _)";
          first done.
      iNext.
      iExists _, _, _.
      iFrame.
      iPureIntro.
      right.
      split; first done.
      by exists vx', vy'.
    }
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
          %Hinv)" "close".
    iModIntro.
    iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}, m,
            {[ "x" := (Some vx, false); "y" := (Some #(-1), false);
                "z" := (hist_val hz, false) ]}.
    iFrame.
    iSplitL "x_upd x_hx x_hx' y_upd y_hy y_hy' z_upd z_hz z_hz'".
    {
      rewrite !dom_insert_L dom_m !dom_empty_L.
      do 2 (iSplit; first done).
      by iSplitL "x_hx' y_hy' z_hz'";
          repeat (iApply big_sepM_insert; first done; iFrame).
    }
    iIntros "!>(_ & [(_ & mem)|(_ & mem)])".
    {
      iMod ("close" with "[mem]") as "_"; last by iApply "HΦ".
      iPoseProof (big_sepM2_insert with "mem") as "((x_hx' & _) & mem)";
        [done..|].
      iPoseProof (big_sepM2_insert with "mem") as "((y_hy' & _) & mem)";
        [done..|].
      iPoseProof (big_sepM2_insert with "mem") as "((z_hz' & _) & _)";
        [done..|].
      have -> : commit_event (hist_val hz, false) hz' = hz'
            by case: (hist_val hz).
      iNext.
      iExists hx', hy', hz'.
      by iFrame.
    }
    iMod ("close" with "[mem]") as "_"; last by iApply "HΦ".
    iPoseProof (big_sepM_insert with "mem") as "((x_hx' & _) & mem)";
      [done..|].
    iPoseProof (big_sepM_insert with "mem") as "((y_hy' & _) & mem)";
      [done..|].
    iPoseProof (big_sepM_insert with "mem") as "((z_hz' & _) & _)";
      [done..|].
    iNext.
    iExists _, _, _.
    by iFrame.
  Qed.

  Lemma transaction4_spec :
    ∀ cst sa,
    client_inv -∗
    {{{ ConnectionState cst CanStart }}}
      transaction4 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ !>CanStart HΦ".
    rewrite/transaction4.
    wp_pures.
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx & %hy & %hz & x_hx & y_hy & z_hz & init)" "close".
    iModIntro.
    iExists {[ "x" := hx; "y" := hy; "z" := hz ]}.
    iFrame.
    iSplitL "x_hx y_hy z_hz";
      first by repeat (iApply big_sepM_insert; first done; iFrame).
    iIntros "!>(Active & mem & cache & Seen)".
    iMod ("close" with "[mem init]") as "_".
    {
      iNext.
      iExists hx, hy, hz.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(z_hz & _)"; first done.
      iFrame.
    }
    iModIntro.
    wp_pures.
    wp_apply (simplified_wait_on_keyT_spec _ _ #1 _ _ _ (⊤ ∖ ↑client_inv_name)
        (λ m, ∃ hx hy hz vx vy, ⌜m !! "x" = Some hx⌝ ∗ ⌜m !! "y" = Some hy⌝ ∗
          ⌜m !! "z" = Some hz⌝ ∗ ⌜#1 ∈ hz⌝ ∗
          ⌜hist_val hx = Some vx⌝ ∗ ⌜hist_val hy = Some vy⌝ ∗
          (⌜vx = #1⌝ ∨ ⌜vx = #(-1)⌝) ∗ (⌜vy = #1⌝ ∨ ⌜vy = #(-1)⌝))%I
          emp emp with
          "[] [] [] [] [] [] [$Active $cache $Seen]"); first solve_ndisj.
    1, 2 : rewrite !dom_insert_L; iPureIntro; set_solver.
    {
      iIntros "!>%h (#Seen & _)".
      iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
          [(_ & _ & ->)|(%hz'_1 & (%vx & %vy & %hx'_vx & %hy'_vy & 
            (%Hvx & %Hvy)))])" "close".
      { iMod (Seen_valid with "[] [$Seen $z_hz']") as "(z_hz' & %abs)";
          [solve_ndisj|iApply SI_GlobalInv|by apply suffix_nil_inv in abs].
      }
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}.
      iSplit; first by rewrite !dom_insert_L.
      iSplitL "x_hx' y_hy' z_hz'";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
      iSplitR.
      {
        iExists hx', hy', hz', vx, vy.
        iFrame "%".
        by rewrite (lookup_insert_ne _ _ "y").
      }
      iSplitR; first done.
      iIntros "!>(mem & _)".
      iMod ("close" with "[mem]") as "_"; last done.
      iNext.
      iExists hx', hy', hz'.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(z_hz' & _)"; first done.
      iFrame.
      iRight.
      iSplit; first done.
      by iExists vx, vy.
    }
    {
      iModIntro.
      iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
          %Hinv)" "close".
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}.
      iSplit; first by rewrite !dom_insert_L.
      iSplitL "x_hx' y_hy' z_hz'";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
      iIntros "!>mem".
      iMod ("close" with "[mem]") as "_"; last done.
      iNext.
      iExists hx', hy', hz'.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(z_hz' & _)"; first done.
      iFrame "∗ %".
    }
    {
      iIntros (v' Ψ) "!>_ HΨ".
      wp_pures.
      wp_op; first apply bin_op_eval_eq_val.
      iApply "HΨ".
      by rewrite bool_decide_spec.
    }
    rewrite !dom_insert_L.
    iClear (hx hy hz) "".
    iIntros (m) "(%dom_m & (%hx & %hy & %hz & %vx & %vy & %m_x & %m_y & %m_z &
          %hz_not_empty & %hx_vx & %hy_vy & %Hvx & %Hvy) & Active & cache & Seen)".
    wp_pures.
    iPoseProof (big_sepM_delete _ _ _ _ m_x with "cache") as
        "((x_hx & x_upd) & cache)".
    iPoseProof (big_sepM_delete _ _ "y" hy with "cache") as
        "((y_hy & y_upd) & cache)"; first by rewrite lookup_delete_ne.
    iPoseProof (big_sepM_delete _ _ "z" hz with "cache") as
        "((z_hz & z_upd) & _)"; first by rewrite !lookup_delete_ne.
    iPoseProof (big_sepM_lookup _ _ _ _ m_z with "Seen") as "#Seen_z".
    wp_apply (SI_read_spec with "[] x_hx"); first set_solver.
    iIntros "x_hx".
    wp_apply wp_unSOME; first by rewrite hx_vx.
    iIntros "_".
    wp_pures.
    wp_apply (SI_read_spec with "[] y_hy"); first set_solver.
    iIntros "y_hy".
    wp_apply wp_unSOME; first by rewrite hy_vy.
    iIntros "_".
    wp_pures.
    iAssert (∀ a b : Z, ⌜vx = #a⌝ ∗ ⌜vy = #b⌝ ∗
        ⌜(a + b ≠ -2)%Z → (0 ≤ a + b)%Z⌝ -∗
        WP let: "r" := vx + vy in
        assert: (if: "r" = #(-2) then #true else #0 ≤ "r") ;; 
        util_code.commitU cst @[ip_of_address sa] {{ v, Φ v }})%I with 
       "[HΦ Active x_upd y_upd z_upd x_hx y_hy z_hz]" as "finish".
    {
      iIntros (a b) "(-> & -> & %Hab)".
      wp_pures.
      rewrite /assert.
      wp_pures.
      case eq: (bool_decide (a + b = -2)%Z).
      {
        wp_pures.
        wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
        iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' & %Hinv)"
                          "close".
        iModIntro.
        iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}, _,
                {[ "x" := (hist_val hx, false); "y" := (hist_val hy, false);
                   "z" := (hist_val hz, false) ]}.
        iFrame.
        iSplitL "x_upd x_hx x_hx' y_upd y_hy y_hy' z_upd z_hz z_hz'".
        {
          rewrite !dom_insert_L dom_m !dom_empty_L.
          do 2 (iSplit; first done).
          by iSplitL "x_hx' y_hy' z_hz'";
             repeat (iApply big_sepM_insert; first done; iFrame).
        }
        iIntros "!>(_ & [(_ & mem)|(_ & mem)])".
        {
          iMod ("close" with "[mem]") as "_"; last by iApply "HΦ".
          iPoseProof (big_sepM2_insert with "mem") as "((x_hx' & _) & mem)";
            [done..|].
          iPoseProof (big_sepM2_insert with "mem") as "((y_hy' & _) & mem)";
            [done..|].
          iPoseProof (big_sepM2_insert with "mem") as "((z_hz' & _) & _)";
            [done..|].
          have -> : commit_event (hist_val hx, false) hx' = hx'
                by case: (hist_val hx).
          have -> : commit_event (hist_val hy, false) hy' = hy'
                by case: (hist_val hy).
          have -> : commit_event (hist_val hz, false) hz' = hz'
                by case: (hist_val hz).
          iNext.
          iExists hx', hy', hz'.
          by iFrame.
        }
        iMod ("close" with "[mem]") as "_"; last by iApply "HΦ".
        iPoseProof (big_sepM_insert with "mem") as "((x_hx' & _) & mem)";
          [done..|].
        iPoseProof (big_sepM_insert with "mem") as "((y_hy' & _) & mem)";
          [done..|].
        iPoseProof (big_sepM_insert with "mem") as "((z_hz' & _) & _)";
          [done..|].
        iNext.
        iExists _, _, _.
        by iFrame.
      }
      wp_pures.
      apply bool_decide_eq_false in eq.
      rewrite bool_decide_true; last by apply Hab.
      wp_pures.
      wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
      iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' & %Hinv)"
                        "close".
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}, _,
              {[ "x" := (hist_val hx, false); "y" := (hist_val hy, false);
                 "z" := (hist_val hz, false) ]}.
      iFrame.
      iSplitL "x_upd x_hx x_hx' y_upd y_hy y_hy' z_upd z_hz z_hz'".
      {
        rewrite !dom_insert_L dom_m !dom_empty_L.
        do 2 (iSplit; first done).
        by iSplitL "x_hx' y_hy' z_hz'";
           repeat (iApply big_sepM_insert; first done; iFrame).
      }
      iIntros "!>(_ & [(_ & mem)|(_ & mem)])".
      {
        iMod ("close" with "[mem]") as "_"; last by iApply "HΦ".
        iPoseProof (big_sepM2_insert with "mem") as "((x_hx' & _) & mem)";
          [done..|].
        iPoseProof (big_sepM2_insert with "mem") as "((y_hy' & _) & mem)";
          [done..|].
        iPoseProof (big_sepM2_insert with "mem") as "((z_hz' & _) & _)";
          [done..|].
        have -> : commit_event (hist_val hx, false) hx' = hx'
              by case: (hist_val hx).
        have -> : commit_event (hist_val hy, false) hy' = hy'
              by case: (hist_val hy).
        have -> : commit_event (hist_val hz, false) hz' = hz'
              by case: (hist_val hz).
        iNext.
        iExists hx', hy', hz'.
        by iFrame.
      }
      iMod ("close" with "[mem]") as "_"; last by iApply "HΦ".
      iPoseProof (big_sepM_insert with "mem") as "((x_hx' & _) & mem)";
        [done..|].
      iPoseProof (big_sepM_insert with "mem") as "((y_hy' & _) & mem)";
        [done..|].
      iPoseProof (big_sepM_insert with "mem") as "((z_hz' & _) & _)";
        [done..|].
      iNext.
      iExists _, _, _.
      by iFrame.
    }
    case: Hvx=>[->|->]; case: Hvy=>[->|->]; iApply "finish";
        do 2 (iSplit; first done); iPureIntro; lia.
  Qed.

  Lemma transaction1_client_spec :
    ∀ sa,
    client_inv -∗
    {{{
      sa ⤳ (∅, ∅) ∗
      unallocated {[sa]} ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      KVS_address ⤇ KVS_si
    }}}
      transaction1_client $sa $KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (sa) "#inv %Φ !>(∅ & unalloc & free & #KVS_si) HΦ".
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
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      KVS_address ⤇ KVS_si
    }}}
      transaction2_client $sa $KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (sa) "#inv %Φ !>(∅ & unalloc & free & #KVS_si) HΦ".
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
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      KVS_address ⤇ KVS_si
    }}}
      transaction3_client $sa $KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (sa) "#inv %Φ !>(∅ & unalloc & free & #KVS_si) HΦ".
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
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      KVS_address ⤇ KVS_si
    }}}
      transaction4_client $sa $KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (sa) "#inv %Φ !>(∅ & unalloc & free & #KVS_si) HΦ".
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
    iMod SI_init_module as (SI_res SI_client_toolbox) "(mem & KVS_Init)".
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
    iSplitR "clt1_∅ clt1_unalloc"; last first.
    {
      iIntros "!>Hports".
      by wp_apply (transaction1_client_spec client_1_addr with "inv [$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "clt2_∅ clt2_unalloc"; last first.
    {
      iIntros "!>Hports".
      by wp_apply (transaction2_client_spec client_2_addr with "inv [$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "clt3_∅ clt3_unalloc"; last first.
    {
      iIntros "!>Hports".
      by wp_apply (transaction3_client_spec client_3_addr with "inv [$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "clt4_∅ clt4_unalloc"; last first.
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
Qed. *)