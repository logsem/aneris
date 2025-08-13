From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import inject.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  time events aux_defs resources specs.
From aneris.examples.transactional_consistency Require Import user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.examples.causality_example
      Require Import causality_example_code.
Import ser_inj.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation Require Import
     snapshot_isolation_api_implementation
     instantiation_of_init.
From aneris.examples.transactional_consistency.snapshot_isolation.util Require Import util_proof.
From aneris.examples.transactional_consistency.snapshot_isolation Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params.

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

  Context `{!anerisG Mdl Σ, !SI_resources Mdl Σ}.

  Definition client_inv_def : iProp Σ :=
    ∃ hx hy, "x" ↦ₖ hx ∗ "y" ↦ₖ hy ∗ (
      (⌜hx = []⌝ ∗ ⌜hy = []⌝) ∨ ⌜last hx = Some #1⌝).

  Definition client_inv : iProp Σ :=
    inv client_inv_name client_inv_def.

  Lemma transaction1_spec :
    ∀ (cst : val) sa,
    SI_client_toolbox -∗
    client_inv -∗
    {{{ ConnectionState cst sa CanStart ∗ IsConnected cst sa }}}
      transaction1 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) #inv %Φ !> (CanStart & #HiC) HΦ".
    rewrite/transaction1.
    wp_pures.
    wp_apply ("Hst" $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; eauto.
    iInv "inv" as ">(%hx & %hy & x_hx & y_hy & Hinv)" "close".
    iModIntro.
    iExists {[ "x" := hx; "y" := hy ]}.
    iFrame.
    iSplitL "x_hx y_hy";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
    iIntros "(Active & mem & cache & _)".
    iPoseProof (big_sepM_insert with "mem") as "(x_hx & mem)"; first done.
    iPoseProof (big_sepM_insert with "mem") as "(y_hy & _)"; first done.
    iMod ("close" with "[x_hx y_hy Hinv]") as "_".
    { iNext. iExists hx, hy. iFrame. }
    iPoseProof (big_sepM_insert with "cache") as "((x_hx & x_upd) & cache)"; first done.
    iPoseProof (big_sepM_insert with "cache") as "((y_hy & y_upd) & _)"; first done.
    iModIntro.
    wp_pures.
    wp_apply ("Hwr" $! _ _ ⊤ _ (SerVal #1) with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _, _.
    iFrame.
    iIntros "(x_1 & x_upd)".
    iModIntro.
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; try eauto.
    iFrame "#".
    iInv "inv" as ">(%hx' & %hy' & x_hx' & y_hy' & Hinv)" "close".
    iModIntro.
    iExists {[ "x" := hx'; "y" := hy' ]}, _,
            {[ "x" := (Some #1, true); "y" := (last hy, false) ]}.
    iFrame.
    iSplitL "x_1 x_hx' x_upd y_hy y_hy' y_upd".
    {
      do 2 (iSplit; first by rewrite !dom_insert_L !dom_empty_L).
      by iSplitL "x_hx' y_hy'";
        repeat (iApply big_sepM_insert; first done; iFrame).
    }
    iIntros "(CanStart & [(_ & mem)|(_ & mem)])".
    {
      iPoseProof (big_sepM2_insert with "mem") as "((x_1 & _) & mem)";
        [done..|].
      iPoseProof (big_sepM2_insert with "mem") as "((y_hy & _) & _)";
        [done..|].
      have -> : commit_event (last hy, false) hy' = hy' by case: (last hy).
      iMod ("close" with "[x_1 y_hy]") as "_".
      { iNext. iExists _, _. iFrame. rewrite last_snoc. by iRight.
      }
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
      GlobalInv -∗
      SI_client_toolbox -∗
    {{{ ConnectionState cst sa CanStart ∗ IsConnected cst sa }}}
      transaction2 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv #ginv (#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (CanStart & #HiC) HΦ".
    rewrite/transaction2.
    wp_pures.
    wp_apply (simple_wait_transaction_spec _ _ #1 _ _ (⊤ ∖ ↑client_inv_name)
        with "[] [] [$] [] [] [] [$CanStart $HiC]");
    [solve_ndisj|set_solver|iFrame "#"|..].
    {
      iModIntro.
      iNext.
      iInv "inv" as ">(%hx & %hy & x_hx & y_hy & %Hinv)" "close".
      iModIntro.
      iExists hx.
      iFrame.
      iIntros "x_hx".
      iMod ("close" with "[x_hx y_hy]") as "_"; last done.
      iNext.
      iExists hx, hy.
      by iFrame.
    }
    {
      iIntros (v Ψ) "!>_ HΨ".
      wp_pures.
      wp_op; first apply bin_op_eval_eq_val.
      iApply "HΨ".
      by rewrite bool_decide_spec.
    }
    iIntros (h) "(CanStart & Seen)".
    wp_pures.
    wp_apply ("Hst" $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; try eauto.
    iInv "inv" as ">(%hx & %hy & x_hx & y_hy & [(-> & _)|%hx_1])" "close".
    {
      iMod (Seen_valid with "[$ginv][$Seen $x_hx]") as "(_ & %abs)";
        first solve_ndisj.
    apply prefix_nil_inv in abs.
    by apply app_nil in abs as [_].
    }
    iModIntro.
    iExists {[ "y" := hy ]}.
    iFrame.
    iSplitL "y_hy"; first by iApply big_sepM_singleton.
    iIntros "(Active & kvs & cache & _)".
    iPoseProof (big_sepM_delete _ _ "y" hy with "kvs") as "(y_hy & _)";
      first done.
    iMod ("close" with "[x_hx y_hy]") as "_".
    {
      iNext.
      iExists hx, hy.
      iFrame.
      by iRight.
    }
    iModIntro.
    iPoseProof (big_sepM_delete _ _ "y" hy with "cache")
        as "((y_hy & y_upd) & _)"; first done.
    wp_pures.
    wp_apply ("Hwr" $! _ _  ⊤ _ (SerVal #1) with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _, _.
    iFrame.
    iIntros "(y_1 & y_upd)".
    iModIntro.
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; try eauto.
    iFrame "#".
    iInv "inv" as ">(%hx' & %hy' & x_hx' & y_hy' & [(-> & _)|Hinv])" "close".
    {
      iMod (Seen_valid with "[$ginv][ $Seen $x_hx']") as "(_ & %abs)";
        first solve_ndisj.
     apply prefix_nil_inv in abs.
    by apply app_nil in abs as [_].
    }
    iModIntro.
    iExists {[ "y" := hy' ]}, _,
            {[ "y" := (Some #1, true) ]}.
    iFrame.
    iSplitL "y_1 y_hy' y_upd".
    {
      do 2 (iSplit; first by rewrite !dom_insert_L !dom_empty_L).
      by iSplitL "y_hy'";
        repeat (iApply big_sepM_insert; first done; iFrame).
    }
    iIntros "(CanStart & [(_ & mem)|(_ & mem)])".
    {
      iPoseProof (big_sepM2_insert with "mem") as "((y_1 & _) & _)";
        [done..|].
      iMod ("close" with "[x_hx' y_1 Hinv]") as "_".
      { iNext. iExists _, _. iFrame. }
      by iApply "HΦ".
    }
    iPoseProof (big_sepM_insert with "mem") as "((y_hy' & _) & mem)"; first done.
    iMod ("close" with "[x_hx' y_hy' Hinv]") as "_".
    { iNext. iExists _, _. iFrame. }
    by iApply "HΦ".
  Qed.

  Lemma transaction3_spec :
    ∀ (cst : val) sa,
      client_inv -∗
      GlobalInv -∗
      SI_client_toolbox -∗
    {{{ ConnectionState cst sa CanStart ∗ IsConnected cst sa }}}
      transaction3 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv #ginv (#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (CanStart & #HiC) HΦ".
    rewrite/transaction3.
    wp_pures.
    wp_apply (simple_wait_transaction_spec _ _ #1 _ _ (⊤ ∖ ↑client_inv_name)
        with "[] [] [$] [] [] [] [$CanStart $HiC]");
    [solve_ndisj|set_solver|iFrame "#"|..].
    {
      iModIntro.
      iNext.
      iInv "inv" as ">(%hx & %hy & x_hx & y_hy & %Hinv)" "close".
      iModIntro.
      iExists hy.
      iFrame.
      iIntros "y_hy".
      iMod ("close" with "[x_hx y_hy]") as "_"; last done.
      iNext.
      iExists hx, hy.
      by iFrame.
    }
    {
      iIntros (v Ψ) "!>_ HΨ".
      wp_pures.
      wp_op; first apply bin_op_eval_eq_val.
      iApply "HΨ".
      by rewrite bool_decide_spec.
    }
    iIntros (h) "(CanStart & Seen)".
    wp_pures.
    wp_apply ("Hst" $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; eauto.
    iInv "inv" as ">(%hx & %hy & x_hx & y_hy & [(_ & ->)|%hx_1])" "close".
    {
      iMod (Seen_valid with "[$ginv][$Seen $y_hy]") as "(_ & %abs)";
        first solve_ndisj.
     apply prefix_nil_inv in abs.
    by apply app_nil in abs as [_].
    }
    iModIntro.
    iExists {[ "x" := hx ]}.
    iFrame.
    iSplitL "x_hx"; first by iApply big_sepM_singleton.
    iIntros "(Active & kvs & cache & _)".
    iPoseProof (big_sepM_delete _ _ "x" hx with "kvs") as "(x_hx & _)";
      first done.
    iMod ("close" with "[x_hx y_hy]") as "_".
    {
      iNext.
      iExists hx, hy.
      iFrame.
      by iRight.
    }
    iModIntro.
    iPoseProof (big_sepM_delete _ _ "x" hx with "cache")
        as "((x_hx & x_upd) & _)"; first done.
    wp_pures.
    wp_apply ("Hrd" $! _ _ ⊤ with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _.
    iFrame.
    iIntros "x_hx".
    iModIntro.
    wp_pures.
    rewrite/assert hx_1.
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; try eauto.
    iFrame "#".
    iInv "inv" as ">(%hx' & %hy' & x_hx' & y_hy' & [(_ & ->)|Hinv])" "close".
    {
      iMod (Seen_valid with "[$ginv][$Seen $y_hy']") as "(_ & %abs)";
        first solve_ndisj.
     apply prefix_nil_inv in abs.
    by apply app_nil in abs as [_].
    }
    iModIntro.
    iExists {[ "x" := hx' ]}, _,
            {[ "x" := (Some #1, false) ]}.
    iFrame.
    iSplitL "x_hx x_hx' x_upd".
    {
      do 2 (iSplit; first by rewrite !dom_insert_L !dom_empty_L).
      by iSplitL "x_hx'";
        repeat (iApply big_sepM_insert; first done; iFrame).
    }
    iIntros "(CanStart & [(_ & mem)|(_ & mem)])".
    {
      iPoseProof (big_sepM2_insert with "mem") as "((x_hx' & _) & _)";
        [done..|].
      iMod ("close" with "[x_hx' y_hy' Hinv]") as "_".
      { iNext. iExists _, _. iFrame. }
      by iApply "HΦ".
    }
    iPoseProof (big_sepM_insert with "mem") as "((x_hx' & _) & mem)"; first done.
    iMod ("close" with "[x_hx' y_hy' Hinv]") as "_".
    { iNext. iExists _, _. iFrame. }
    by iApply "HΦ".
  Qed.

  Lemma transaction1_client_spec :
    ∀ clt,
    client_inv -∗
    SI_client_toolbox -∗
    {{{
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_si ∗
      unallocated {[clt]} ∗
      KVS_ClientCanConnect clt ∗
      free_ports (ip_of_address clt) {[port_of_address clt]}
    }}}
      transaction1_client #clt #KVS_address @[ip_of_address clt]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (clt) "#inv (#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (∅ & #KVS_si & unalloc & Hcc & free) HΦ".
    rewrite/transaction1_client.
    wp_pures.
    wp_apply ("Hinit_cli" with "[$∅ $unalloc $free $KVS_si $Hcc]").
    iIntros (cst) "CanStart".
    wp_pures.
    wp_apply (transaction1_spec with "[] [$inv] [$CanStart]").
    iFrame "#".
    done.
  Qed.

  Lemma transaction2_client_spec :
    ∀ clt,
      client_inv -∗
      GlobalInv -∗
      SI_client_toolbox -∗
    {{{
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_si ∗
      unallocated {[clt]} ∗
      KVS_ClientCanConnect clt ∗
      free_ports (ip_of_address clt) {[port_of_address clt]}
    }}}
      transaction2_client #clt #KVS_address @[ip_of_address clt]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (clt) "#inv #ginv (#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (∅ & #KVS_si & unalloc & Hcc & free) HΦ".
    rewrite/transaction2_client.
    wp_pures.
    wp_apply ("Hinit_cli" with "[$∅ $unalloc $free $KVS_si $Hcc]").
    iIntros (cst) "CanStart".
    wp_pures.
    wp_apply (transaction2_spec with "[$inv] [$ginv] [] [$CanStart]").
    iFrame "#".
    done.
  Qed.

  Lemma transaction3_client_spec :
    ∀ clt,
      client_inv -∗
      GlobalInv -∗
      SI_client_toolbox -∗
    {{{
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_si ∗
      unallocated {[clt]} ∗
      KVS_ClientCanConnect clt ∗
      free_ports (ip_of_address clt) {[port_of_address clt]}
    }}}
      transaction3_client #clt #KVS_address @[ip_of_address clt]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (clt) "#inv #ginv (#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (∅ & #KVS_si & unalloc & Hcc & free) HΦ".
    rewrite/transaction3_client.
    wp_pures.
    wp_apply ("Hinit_cli" with "[$∅ $unalloc $free $KVS_si $Hcc]").
    iIntros (cst) "CanStart".
    wp_pures.
    wp_apply (transaction3_spec with "[$inv] [$ginv] [] [$CanStart]").
    iFrame "#".
    done.
  Qed.

  Lemma server_spec :
    SI_client_toolbox -∗
    {{{
      KVS_Init ∗
      KVS_address ⤳ (∅, ∅) ∗
      free_ports (ip_of_address KVS_address) {[port_of_address KVS_address]} ∗
      KVS_address ⤇ KVS_si
    }}}
      server #KVS_address @[ip_of_address KVS_address]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (KVS_Init & ∅ & free & #KVS_si) HΦ".
    rewrite/server.
    wp_pures.
    by wp_apply ("Hinit_kvs" with "[$KVS_si $KVS_Init $∅ $free]").
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
    iMod (SI_init_module _ {[client1_addr; client2_addr; client3_addr]})
      as (SI_res) "(mem & KVS_Init & #Hginv & Hcc & #specs)";
         first done.
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
    { iIntros "!>free". by wp_apply (server_spec with "[$] [$]"). }
    iNext.
    wp_pures.
    iDestruct (big_sepS_delete _  _ client1_addr with "Hcc")
      as "(Hcc1 & Hcc)";
      first set_solver.
    iDestruct (big_sepS_delete _  _ client2_addr with "Hcc")
      as "(Hcc2 & Hcc)";
      first set_solver.
    iDestruct (big_sepS_delete _  _ client3_addr with "Hcc")
      as "(Hcc3 & Hcc)";
      first set_solver.
    wp_apply (aneris_wp_start {[80%positive]}).
    iSplitL "clt1_free"; first done.
    iSplitR "clt1_∅ clt1_unalloc Hcc1"; last first.
    {
      iIntros "!>free".
      by wp_apply (transaction1_client_spec client1_addr with "inv [$] [$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iSplitL "clt2_free"; first done.
    iSplitR "clt2_∅ clt2_unalloc Hcc2"; last first.
    {
      iIntros "!>free".
      by wp_apply (transaction2_client_spec client2_addr with "inv Hginv [$] [$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iSplitL "clt3_free"; first done.
    iSplitR "clt3_∅ clt3_unalloc Hcc3"; last first.
    {
      iIntros "!>free".
      by wp_apply (transaction3_client_spec client3_addr with "inv Hginv [$] [$]").
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
    state_trace := [];
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
Qed.
