(* From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params resources specs.
From aneris.aneris_lang.lib Require Import inject.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.snapshot_isolation.examples.causality_example
      Require Import causality_example_code.
Import ser_inj.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.
From aneris.examples.snapshot_isolation.util Require Import util_proof.
From aneris.examples.snapshot_isolation Require Import snapshot_isolation_code.

Definition server_addr := SocketAddressInet "0.0.0.0" 80.
Definition client1_addr := SocketAddressInet "0.0.0.1" 80.
Definition client2_addr := SocketAddressInet "0.0.0.2" 80.
Definition client3_addr := SocketAddressInet "0.0.0.3" 80.

Instance params : User_params :=
{| KVS_address := server_addr;
  KVS_keys := {["x"; "y"]};
  KVS_InvName := nroot .@ "siinv";
  KVS_serialization := int_serialization;
  KVS_ser_inj := int_ser_is_ser_injective;
  KVS_ser_inj_alt := int_ser_is_ser_injective_alt
|}.

Definition client_inv_name := nroot.@"clinv".

Section proof_of_code.

  Context `{!anerisG Mdl Σ, !SI_resources Mdl Σ, !SI_client_toolbox}.

  Definition client_inv_def : iProp Σ :=
    ∃ hx hy, "x" ↦ₖ hx ∗ "y" ↦ₖ hy ∗ (
      (⌜hx = []⌝ ∗ ⌜hy = []⌝) ∨ ⌜hist_val hx = Some #1⌝).

  Definition client_inv : iProp Σ :=
    inv client_inv_name client_inv_def.

  Lemma transaction1_spec :
    ∀ (cst : val) sa,
    client_inv -∗
    {{{ ConnectionState cst CanStart }}}
      transaction1 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ !> CanStart HΦ".
    rewrite/transaction1.
    wp_pures.
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx & %hy & x_hx & y_hy & Hinv)" "close".
    iModIntro.
    iExists {[ "x" := hx; "y" := hy ]}.
    iFrame.
    iSplitL "x_hx y_hy";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
    iIntros "!>(Active & mem & cache & _)".
    iPoseProof (big_sepM_insert with "mem") as "(x_hx & mem)"; first done.
    iPoseProof (big_sepM_insert with "mem") as "(y_hy & _)"; first done.
    iMod ("close" with "[x_hx y_hy Hinv]") as "_".
    { iNext. iExists hx, hy. iFrame. }
    iPoseProof (big_sepM_insert with "cache") as "((x_hx & x_upd) & cache)"; first done.
    iPoseProof (big_sepM_insert with "cache") as "((y_hy & y_upd) & _)"; first done.
    iModIntro.
    wp_pures.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #1) with "[] [$x_hx $x_upd]");
          first set_solver.
    iIntros "(x_1 & x_upd)".
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx' & %hy' & x_hx' & y_hy' & Hinv)" "close".
    iModIntro.
    iExists {[ "x" := hx'; "y" := hy' ]}, _,
            {[ "x" := (Some #1, true); "y" := (hist_val hy, false) ]}.
    iFrame.
    iSplitL "x_1 x_hx' x_upd y_hy y_hy' y_upd".
    {
      do 2 (iSplit; first by rewrite !dom_insert_L !dom_empty_L).
      by iSplitL "x_hx' y_hy'";
        repeat (iApply big_sepM_insert; first done; iFrame).
    }
    iIntros "!>(CanStart & [(_ & mem)|(_ & mem)])".
    {
      iPoseProof (big_sepM2_insert with "mem") as "((x_1 & _) & mem)";
        [done..|].
      iPoseProof (big_sepM2_insert with "mem") as "((y_hy & _) & _)";
        [done..|].
      have -> : commit_event (hist_val hy, false) hy' = hy' by case: (hist_val hy).
      iMod ("close" with "[x_1 y_hy]") as "_".
      { iNext. iExists _, _. iFrame. by iRight. }
      by iApply "HΦ".
    }
    iPoseProof (big_sepM_insert with "mem") as "((x_hx' & _) & mem)"; first done.
    iPoseProof (big_sepM_insert with "mem") as "((y_hy' & _) & mem)"; first done.
    iMod ("close" with "[x_hx' y_hy' Hinv]") as "_".
    { iNext. iExists _, _. iFrame. }
    by iApply "HΦ".
  Qed.

  Lemma transaction2_spec :
    ∀ (cst : val) sa,
    client_inv -∗
    {{{ ConnectionState cst CanStart }}}
      transaction2 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ !> CanStart HΦ".
    rewrite/transaction2.
    wp_pures.
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx & %hy & x_hx & y_hy & Hinv)" "close".
    iModIntro.
    iExists {[ "x" := hx; "y" := hy ]}.
    iFrame.
    iSplitL "x_hx y_hy";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
    iIntros "!>(Active & mem & cache & Seen)".
    iPoseProof (big_sepM_insert with "mem") as "(x_hx & mem)"; first done.
    iPoseProof (big_sepM_insert with "mem") as "(y_hy & _)"; first done.
    iMod ("close" with "[x_hx y_hy Hinv]") as "_".
    { iNext. iExists hx, hy. iFrame. }
    iModIntro.
    wp_pures.
    wp_apply (simplified_wait_on_keyT_spec _ _ #1 _ _ _ (⊤ ∖ ↑client_inv_name)
          (λ m, ∃ h, ⌜m !! "x" = Some h⌝ ∗ ⌜hist_val h = Some #1⌝)%I emp emp
          with "[] [] [] [] [] [] [$Active $cache $Seen]"); first solve_ndisj.
    1, 2 : rewrite !dom_insert_L dom_empty_L; iPureIntro; set_solver.
    {
      iIntros "!>%h (#Seen_x & _)".
      iInv "inv" as ">(%hx' & %hy' & x_hx' & y_hy' & [(-> & _)|%Hhx'])" "close".
      {
        iMod (Seen_valid $! SI_GlobalInv with "[$Seen_x $x_hx']") as "(_ & %abs)";
          first solve_ndisj.
        by apply suffix_nil_inv in abs.
      }
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy' ]}.
      rewrite !dom_insert_L dom_empty_L.
      iSplit; first done.
      iSplitL "x_hx' y_hy'";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
      iSplit; first (iExists hx'; rewrite lookup_insert; by iFrame "%").
      iSplit; first done.
      iIntros "!>(mem & _)".
      iPoseProof (big_sepM_insert with "mem") as "(x_hx' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy' & _)"; first done.
      iMod ("close" with "[x_hx' y_hy']") as "_"; last done.
      iNext.
      iExists _, _.
      iFrame.
      by iRight.
    }
    {
      iModIntro.
      iInv "inv" as ">(%hx' & %hy' & x_hx' & y_hy' & %Hinv)" "close".
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy' ]}.
      rewrite !dom_insert_L dom_empty_L.
      iSplit; first done.
      iSplitL "x_hx' y_hy'";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
      iIntros "!>mem".
      iPoseProof (big_sepM_insert with "mem") as "(x_hx' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy' & _)"; first done.
      iMod ("close" with "[x_hx' y_hy']") as "_"; last done.
      iNext.
      iExists _, _.
      iFrame "∗%".
    }
    {
      iIntros (v' Ψ) "!>_ HΨ".
      wp_pures.
      wp_op; first apply bin_op_eval_eq_val.
      iApply "HΨ".
      by rewrite bool_decide_spec.
    }
    rewrite !dom_insert_L dom_empty_L.
    iClear (hx hy) "".
    iIntros (m) "(%dom_m & (%h & %m_x & %Hhx) & Active & cache & Seen)".
    wp_pures.
    iPoseProof (big_sepM_delete _ _ _ _ m_x with "cache") as "((x_h & x_upd) & cache)".
    have y_key : "y" ∈ dom (delete "x" m) by set_solver.
    destruct ((proj1 (elem_of_dom _ _)) y_key) as [h' m_y].
    iPoseProof (big_sepM_delete _ _ _ _ m_y with "cache") as "((y_h' & y_upd) & _)".
    iPoseProof (big_sepM_lookup _ _ _ _ m_x with "Seen") as "#Seen_x".
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #1) with "[] [$y_h' $y_upd]");
          first set_solver.
    iIntros "(y_1 & y_upd)".
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx' & %hy' & x_hx' & y_hy' & [(-> & _)|Hinv])" "close".
    {
      iMod (Seen_valid $! SI_GlobalInv with "[$Seen_x $x_hx']") as "(_ & %abs)";
        first solve_ndisj.
      apply suffix_nil_inv in abs.
      by rewrite abs in Hhx.
    }
    iModIntro.
    iExists {[ "x" := hx'; "y" := hy' ]}, _,
            {[ "x" := (Some #1, false); "y" := (Some #1, true) ]}.
    iFrame.
    rewrite Hhx.
    iSplitL "x_h x_hx' x_upd y_1 y_hy' y_upd".
    {
      do 2 (iSplit; first by rewrite !dom_insert_L !dom_empty_L).
      by iSplitL "x_hx' y_hy'";
        repeat (iApply big_sepM_insert; first done; iFrame).
    }
    iIntros "!>(CanStart & [(_ & mem)|(_ & mem)])".
    {
      iPoseProof (big_sepM2_insert with "mem") as "((x_hx' & _) & mem)";
        [done..|].
      iPoseProof (big_sepM2_insert with "mem") as "((y_1 & _) & _)";
        [done..|].
      iMod ("close" with "[x_hx' y_1 Hinv]") as "_".
      { iNext. iExists _, (#1 :: hy'). iFrame. }
      by iApply "HΦ".
    }
    iPoseProof (big_sepM_insert with "mem") as "((x_hx' & _) & mem)"; first done.
    iPoseProof (big_sepM_insert with "mem") as "((y_hy' & _) & mem)"; first done.
    iMod ("close" with "[x_hx' y_hy' Hinv]") as "_".
    { iNext. iExists _, _. iFrame. }
    by iApply "HΦ".
  Qed.

  Lemma transaction3_spec :
    ∀ (cst : val) sa,
    client_inv -∗
    {{{ ConnectionState cst CanStart }}}
      transaction3 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ !> CanStart HΦ".
    rewrite/transaction3.
    wp_pures.
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx & %hy & x_hx & y_hy & Hinv)" "close".
    iModIntro.
    iExists {[ "x" := hx; "y" := hy ]}.
    iFrame.
    iSplitL "x_hx y_hy";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
    iIntros "!>(Active & mem & cache & Seen)".
    iPoseProof (big_sepM_insert with "mem") as "(x_hx & mem)"; first done.
    iPoseProof (big_sepM_insert with "mem") as "(y_hy & _)"; first done.
    iMod ("close" with "[x_hx y_hy Hinv]") as "_".
    { iNext. iExists hx, hy. iFrame. }
    iModIntro.
    wp_pures.
    wp_apply (simplified_wait_on_keyT_spec _ _ #1 _ _ _ (⊤ ∖ ↑client_inv_name)
          (λ m, ∃ h, ⌜m !! "x" = Some h⌝ ∗ ⌜hist_val h = Some #1⌝)%I emp emp
          with "[] [] [] [] [] [] [$Active $cache $Seen]"); first solve_ndisj.
    1, 2 : rewrite !dom_insert_L dom_empty_L; iPureIntro; set_solver.
    {
      iIntros "!>%h (#Seen_y & _)".
      iInv "inv" as ">(%hx' & %hy' & x_hx' & y_hy' & [(_ & ->)|%Hhx'])" "close".
      {
        iMod (Seen_valid $! SI_GlobalInv with "[$Seen_y $y_hy']") as "(_ & %abs)";
          first solve_ndisj.
        by apply suffix_nil_inv in abs.
      }
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy' ]}.
      rewrite !dom_insert_L dom_empty_L.
      iSplit; first done.
      iSplitL "x_hx' y_hy'";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
      iSplit; first (iExists hx'; rewrite lookup_insert; by iFrame "%").
      iSplit; first done.
      iIntros "!>(mem & _)".
      iPoseProof (big_sepM_insert with "mem") as "(x_hx' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy' & _)"; first done.
      iMod ("close" with "[x_hx' y_hy']") as "_"; last done.
      iNext.
      iExists _, _.
      iFrame.
      by iRight.
    }
    {
      iModIntro.
      iInv "inv" as ">(%hx' & %hy' & x_hx' & y_hy' & %Hinv)" "close".
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy' ]}.
      rewrite !dom_insert_L dom_empty_L.
      iSplit; first done.
      iSplitL "x_hx' y_hy'";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
      iIntros "!>mem".
      iPoseProof (big_sepM_insert with "mem") as "(x_hx' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy' & _)"; first done.
      iMod ("close" with "[x_hx' y_hy']") as "_"; last done.
      iNext.
      iExists _, _.
      iFrame "∗%".
    }
    {
      iIntros (v' Ψ) "!>_ HΨ".
      wp_pures.
      wp_op; first apply bin_op_eval_eq_val.
      iApply "HΨ".
      by rewrite bool_decide_spec.
    }
    rewrite !dom_insert_L dom_empty_L.
    iClear (hx hy) "".
    iIntros (m) "(%dom_m & (%h & %m_x & %Hhx) & Active & cache & Seen)".
    wp_pures.
    iPoseProof (big_sepM_delete _ _ _ _ m_x with "cache") as "((x_h & x_upd) & cache)".
    have y_key : "y" ∈ dom (delete "x" m) by set_solver.
    destruct ((proj1 (elem_of_dom _ _)) y_key) as [h' m_y].
    iPoseProof (big_sepM_delete _ _ _ _ m_y with "cache") as "((y_h' & y_upd) & _)".
    iPoseProof (big_sepM_lookup _ _ _ _ m_x with "Seen") as "#Seen_x".
    wp_apply (SI_read_spec with "[] [$x_h]");
          first set_solver.
    iIntros "x_h".
    rewrite Hhx/assert.
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx' & %hy' & x_hx' & y_hy' & [(-> & _)|Hinv])" "close".
    {
      iMod (Seen_valid $! SI_GlobalInv with "[$Seen_x $x_hx']") as "(_ & %abs)";
        first solve_ndisj.
      apply suffix_nil_inv in abs.
      by rewrite abs in Hhx.
    }
    iModIntro.
    iExists {[ "x" := hx'; "y" := hy' ]}, _,
            {[ "x" := (Some #1, false); "y" := (hist_val h', false) ]}.
    iFrame.
    iSplitL "x_h x_hx' x_upd y_h' y_hy' y_upd".
    {
      do 2 (iSplit; first by rewrite !dom_insert_L !dom_empty_L).
      by iSplitL "x_hx' y_hy'";
        repeat (iApply big_sepM_insert; first done; iFrame).
    }
    iIntros "!>(CanStart & [(_ & mem)|(_ & mem)])".
    {
      iPoseProof (big_sepM2_insert with "mem") as "((x_hx' & _) & mem)";
        [done..|].
      iPoseProof (big_sepM2_insert with "mem") as "((y_hy' & _) & _)";
        [done..|].
      have -> : commit_event (hist_val h', false) hy' = hy' by case: (hist_val h').
      iMod ("close" with "[x_hx' y_hy' Hinv]") as "_".
      { iNext. iExists _, _. iFrame. }
      by iApply "HΦ".
    }
    iPoseProof (big_sepM_insert with "mem") as "((x_hx' & _) & mem)"; first done.
    iPoseProof (big_sepM_insert with "mem") as "((y_hy' & _) & mem)"; first done.
    iMod ("close" with "[x_hx' y_hy' Hinv]") as "_".
    { iNext. iExists _, _. iFrame. }
    by iApply "HΦ".
  Qed.

  Lemma transaction1_client_spec :
    ∀ clt,
    client_inv -∗
    {{{
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_si ∗
      unallocated {[clt]} ∗
      free_ports (ip_of_address clt) {[port_of_address clt]}
    }}}
      transaction1_client #clt #KVS_address @[ip_of_address clt]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (clt) "#inv %Φ !> (∅ & #KVS_si & unalloc & free) HΦ".
    rewrite/transaction1_client.
    wp_pures.
    wp_apply (SI_init_client_proxy_spec with "[$∅ $unalloc $free $KVS_si]").
    iIntros (cst) "CanStart".
    wp_pures.
    by wp_apply (transaction1_spec with "inv CanStart").
  Qed.

  Lemma transaction2_client_spec :
    ∀ clt,
    client_inv -∗
    {{{
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_si ∗
      unallocated {[clt]} ∗
      free_ports (ip_of_address clt) {[port_of_address clt]}
    }}}
      transaction2_client #clt #KVS_address @[ip_of_address clt]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (clt) "#inv %Φ !> (∅ & #KVS_si & unalloc & free) HΦ".
    rewrite/transaction2_client.
    wp_pures.
    wp_apply (SI_init_client_proxy_spec with "[$∅ $unalloc $free $KVS_si]").
    iIntros (cst) "CanStart".
    wp_pures.
    by wp_apply (transaction2_spec with "inv CanStart").
  Qed.

  Lemma transaction3_client_spec :
    ∀ clt,
    client_inv -∗
    {{{
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_si ∗
      unallocated {[clt]} ∗
      free_ports (ip_of_address clt) {[port_of_address clt]}
    }}}
      transaction3_client #clt #KVS_address @[ip_of_address clt]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (clt) "#inv %Φ !> (∅ & #KVS_si & unalloc & free) HΦ".
    rewrite/transaction3_client.
    wp_pures.
    wp_apply (SI_init_client_proxy_spec with "[$∅ $unalloc $free $KVS_si]").
    iIntros (cst) "CanStart".
    wp_pures.
    by wp_apply (transaction3_spec with "inv CanStart").
  Qed.

  Lemma server_spec :
    {{{
      KVS_Init ∗
      KVS_address ⤳ (∅, ∅) ∗
      free_ports (ip_of_address KVS_address) {[port_of_address KVS_address]} ∗
      KVS_address ⤇ KVS_si
    }}}
      server #KVS_address @[ip_of_address KVS_address]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(KVS_Init & ∅ & free & #KVS_si) HΦ".
    rewrite/server.
    wp_pures.
    by wp_apply (SI_init_kvs_spec with "[$KVS_si $KVS_Init $∅ $free]").
  Qed.

End proof_of_code.

Section proof_of_runner.

  Context `{!anerisG Mdl Σ, !SI_init, !KVSG Σ}.

  Definition runner : expr :=
    Start "0.0.0.0" (server #KVS_address) ;;
    Start "0.0.0.1" (transaction1_client #client1_addr #KVS_address) ;;
    Start "0.0.0.2" (transaction2_client #client2_addr #KVS_address) ;;
    Start "0.0.0.3" (transaction3_client #client3_addr #KVS_address).

  Lemma runner_spec :
    {{{
      server_addr ⤳ (∅, ∅) ∗
      client1_addr ⤳ (∅, ∅) ∗
      client2_addr ⤳ (∅, ∅) ∗
      client3_addr ⤳ (∅, ∅) ∗
      unallocated {[server_addr]} ∗
      unallocated {[client1_addr]} ∗
      unallocated {[client2_addr]} ∗
      unallocated {[client3_addr]} ∗
      free_ip (ip_of_address server_addr) ∗
      free_ip (ip_of_address client1_addr) ∗
      free_ip (ip_of_address client2_addr) ∗
      free_ip (ip_of_address client3_addr)
    }}}
      runner @["system"]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(srv_∅ & clt1_∅ & clt2_∅ & clt3_∅ & srv_unalloc & clt1_unalloc &
            clt2_unalloc & clt3_unalloc & srv_free & clt1_free & clt2_free & clt3_free)
              HΦ".
    rewrite/runner.
    iMod SI_init_module as "(% & % & mem & KVS_Init)".
    iPoseProof (big_sepS_insert with "mem") as "(x_mem & mem)"; first done.
    iPoseProof (big_sepS_delete _ _ "y" with "mem") as "(y_mem & _)";
      first set_solver.
    iMod (inv_alloc client_inv_name _ client_inv_def with "[x_mem y_mem]") as "#inv".
    { iNext. iExists _, _. iFrame. by iLeft. }
    wp_apply (aneris_wp_socket_interp_alloc_singleton KVS_si with "srv_unalloc").
    iIntros "#KVS_si".
    wp_apply (aneris_wp_start {[80%positive]}).
    iSplitL "srv_free"; first done.
    iSplitR "KVS_Init srv_∅"; last first.
    { iIntros "!>free". by wp_apply (server_spec with "[$]"). }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iSplitL "clt1_free"; first done.
    iSplitR "clt1_∅ clt1_unalloc"; last first.
    {
      iIntros "!>free".
      by wp_apply (transaction1_client_spec client1_addr with "inv [$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iSplitL "clt2_free"; first done.
    iSplitR "clt2_∅ clt2_unalloc"; last first.
    {
      iIntros "!>free".
      by wp_apply (transaction2_client_spec client2_addr with "inv [$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iSplitL "clt3_free"; first done.
    iSplitR "clt3_∅ clt3_unalloc"; last first.
    {
      iIntros "!>free".
      by wp_apply (transaction3_client_spec client3_addr with "inv [$]").
    }
    iNext.
    by iApply "HΦ".
  Qed.

End proof_of_runner.

Definition unit_model := model _ (λ _ _, False) ().

Lemma unit_model_rel_finitary : aneris_model_rel_finitary unit_model.
Proof. intros ?. apply finite_smaller_card_nat. apply _. Qed.

Definition ips : gset ip_address :=
  {[ ip_of_address server_addr ; ip_of_address client1_addr
  ; ip_of_address client2_addr ; ip_of_address client3_addr ]}.

Definition sa_dom : gset socket_address :=
  {[ server_addr ; client1_addr; client2_addr; client3_addr ]}.

Definition init_state :=
  {|
    state_heaps := {["system" := ∅ ]};
    state_sockets := {["system" := ∅ ]};
    state_ms := ∅;
  |}.

Theorem runner_safe :
  aneris_adequate runner "system" init_state (λ _, True).
Proof.
  set (Σ := #[anerisΣ unit_model; KVSΣ]).
  apply (@adequacy Σ unit_model _ _ ips sa_dom ∅ ∅ ∅);
    [apply unit_model_rel_finitary|move=>?|set_solver..].
  iIntros "!> Hunallocated Hhist Hfrag Hips Hlbl _ _ _ _".
  iApply (runner_spec with "[Hunallocated Hhist Hfrag Hips Hlbl]" ).
  2 : { iModIntro. done. }
  do 3 (iDestruct (unallocated_split with "Hunallocated") as "[Hunallocated ?]";
  [set_solver|]). iFrame.
  do 3 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
  iDestruct "Hhist" as "[Hhist ?]"; iFrame).
  do 3 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
  iDestruct "Hips" as "[Hips ?]"; iFrame).
Qed. *)
