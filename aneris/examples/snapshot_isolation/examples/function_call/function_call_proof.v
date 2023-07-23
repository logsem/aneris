From aneris.aneris_lang Require Import network resources proofmode.
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
From aneris.examples.snapshot_isolation.examples.function_call
      Require Import function_call_code.
Import ser_inj.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.
From aneris.examples.snapshot_isolation.util Require Import util_proof.
From aneris.examples.snapshot_isolation Require Import snapshot_isolation_code.

Definition server_addr := SocketAddressInet "0.0.0.0" 80.
Definition client1_addr := SocketAddressInet "0.0.0.1" 80.
Definition client2_addr := SocketAddressInet "0.0.0.2" 80.

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

  Definition f_spec (f : val) : iProp Σ :=
    ∀ (k : Key) cst vo sa,
    ⌜k ∈ KVS_keys⌝ -∗
    {{{ IsConnected cst ∗ k ↦{cst} vo }}}
      f cst #k @[ip_of_address sa]
    {{{ v', RET (SV_val v'); k ↦{cst} vo }}}.

  Definition client_inv_def : iProp Σ :=
    ∃ h, "x" ↦ₖ h.

  Definition client_inv : iProp Σ :=
    inv client_inv_name client_inv_def.

  Lemma transaction1_spec :
    ∀ (cst : val) sa,
    client_inv -∗
    {{{ ConnectionState cst CanStart ∗ IsConnected cst }}}
      transaction1 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ !> (CanStart & #HiC) HΦ".
    rewrite/transaction1.
    wp_pures.
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%h & x_h)" "close".
    iModIntro.
    iExists {[ "x" := h ]}.
    iFrame.
    iSplitL "x_h"; first iApply (big_sepM_singleton with "x_h").
    iIntros "!>(Active & mem & cache & _)".
    iPoseProof (big_sepM_insert with "mem") as "(x_h & _)"; first done.
    iMod ("close" with "[x_h]") as "_".
    { iNext. by iExists h. }
    iPoseProof (big_sepM_insert with "cache") as "((x_h & x_upd) & _)"; first done.
    iModIntro.
    wp_pures.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #42) with "[] [$x_h $x_upd $HiC]");
          first set_solver.
    iIntros "(x_42 & x_upd)".
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%h' & x_h')" "close".
    iModIntro.
    iExists {[ "x" := h' ]}, _, {[ "x" := (Some #42, true) ]}.
    iFrame.
    iSplitL "x_42 x_h' x_upd".
    {
      do 2 (iSplit; first by rewrite 2!dom_singleton_L).
      iSplitL "x_h'"; first iApply (big_sepM_singleton with "x_h'").
      iApply big_sepM_singleton.
      iFrame.
    }
    iIntros "!>(CanStart & [(_ & mem)|(_ & mem)])".
    {
      iPoseProof (big_sepM2_insert with "mem") as "((x_42 & _) & _)";
        [done..|].
      iMod ("close" with "[x_42]") as "_".
      { iNext. iExists _. iFrame. }
      iModIntro.
      iApply ("HΦ" with "[//]").
    }
    iPoseProof (big_sepM_insert with "mem") as "((x_h' & _) & _)"; first done.
    iMod ("close" with "[x_h']") as "_".
    { iNext. iExists h'. iFrame. }
    iModIntro.
    iApply ("HΦ" with "[//]").
  Qed.

  Lemma transaction2_spec :
    ∀ (cst f : val) sa h,
    f_spec f -∗
    client_inv -∗
    {{{ ConnectionState cst CanStart ∗ IsConnected cst ∗ "y" ↦ₖ h }}}
      transaction2 cst f @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst f sa hy) "#f_spec #inv %Φ !>(CanStart & #HiC & y_hy) HΦ".
    rewrite/transaction2.
    wp_pures.
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx & x_hx)" "close".
    iModIntro.
    iExists {[ "x" := hx; "y" := hy ]}.
    iFrame.
    iSplitL "x_hx y_hy".
    {
      iApply big_sepM_insert; first done.
      iFrame.
      iApply (big_sepM_singleton with "y_hy").
    }
    iIntros "!>(Active & mem & cache & _)".
    iPoseProof (big_sepM_insert with "mem") as "(x_hx & mem)"; first done.
    iPoseProof (big_sepM_insert with "mem") as "(y_hy & _)"; first done.
    iMod ("close" with "[x_hx]") as "_".
    { iNext. iExists hx. iFrame. }
    iPoseProof (big_sepM_insert with "cache") as "((cache_x & x_upd) & cache)";
        first done.
    iPoseProof (big_sepM_insert with "cache") as "((cache_y & y_upd) & _)";
        first done.
    iModIntro.
    wp_pures.
    wp_apply ("f_spec" with "[] [$cache_x $HiC]"); first set_solver.
    iIntros (v') "cache_x".
    wp_pures.
    wp_apply (SI_write_spec with "[] [$cache_y $y_upd $HiC]"); first set_solver.
    iIntros "(cache_y & y_upd)".
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx' & x_hx')" "close".
    iModIntro.
    iExists {[ "x" := hx'; "y" := hy ]}, _,
        {[ "x" := (last hx, false); "y" := (Some (SV_val v'), true) ]}.
    iFrame.
    iSplitL "cache_x x_upd cache_y y_upd x_hx' y_hy".
    {
      rewrite !dom_insert_L !dom_empty_L.
      do 2 (iSplit; first done).
      by iSplitL "x_hx' y_hy";
        repeat (iApply big_sepM_insert; first done; iFrame).
    }
    iIntros "!>(CanStart & [(_ & mem) | (_ & mem)])".
    {
      iPoseProof (big_sepM2_insert with "mem") as "((mem_x & _) & _)";
          [done..|].
      iMod ("close" with "[mem_x]") as "_".
      { iNext. by iExists _. }
      iApply ("HΦ" with "[//]").
    }
    iPoseProof (big_sepM_insert with "mem") as "((mem_x & _) & _)"; first done.
    iMod ("close" with "[mem_x]") as "_".
    { iNext. by iExists _. }
    iApply ("HΦ" with "[//]").
  Qed.

  Lemma transaction1_client_spec :
    ∀ clt,
    client_inv -∗
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
    iIntros (clt) "#inv %Φ !> (∅ & #KVS_si & unalloc & Hcc & free) HΦ".
    rewrite/transaction1_client.
    wp_pures.
    wp_apply (SI_init_client_proxy_spec with
               "[$∅ $unalloc $free $KVS_si $Hcc]").
    iIntros (cst) "CanStart".
    wp_pures.
    by wp_apply (transaction1_spec with "inv CanStart").
  Qed.

  Lemma transaction2_client_spec :
    ∀ clt f h,
    client_inv -∗
    f_spec f -∗
    {{{
      "y" ↦ₖ h ∗
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_si ∗
      unallocated {[clt]} ∗
      KVS_ClientCanConnect clt ∗
      free_ports (ip_of_address clt) {[port_of_address clt]}
    }}}
      transaction2_client #clt #KVS_address f @[ip_of_address clt]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (clt f h) "#inv #f_spec %Φ !> (y_h & ∅ & #KVS_si & unalloc
 & Hcc & free) HΦ".
    rewrite/transaction2_client.
    wp_pures.
    wp_apply (SI_init_client_proxy_spec with "[$∅ $unalloc $free $KVS_si $Hcc]").
    iIntros (cst) "(CanStart & HiC)".
    wp_pures.
    by wp_apply (transaction2_spec with "f_spec inv [$CanStart $HiC $y_h]").
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

  Definition f : val :=
    λ: "cst" "k",
      match: read "cst" "k" with
          SOME "v" => "v"
        | NONE     => #0
      end.

  Lemma f_spec_holds `{!SI_resources Mdl Σ, !SI_client_toolbox} :
    ⊢ f_spec f.
  Proof.
    iIntros (k cst vo sa k_keys Φ) "!>(#HiC & k_vo) HΦ".
    rewrite/f.
    wp_pures.
    wp_apply (SI_read_spec with "[//] [$k_vo $HiC]").
    iIntros "k_vo".
    case: vo=>[v|].
    {
      iDestruct (OwnLocalKey_serializable with "[$k_vo]")
        as "(k_vo & %v_ser)".
      wp_pures.
      by iApply ("HΦ" $! (SerVal v)).
    }
    wp_pures.
    by iApply ("HΦ" $! (SerVal #0)).
  Qed.

  Definition runner : expr :=
    Start "0.0.0.0" (server #KVS_address) ;;
    Start "0.0.0.1" (transaction1_client #client1_addr #KVS_address) ;;
    Start "0.0.0.2" (transaction2_client #client2_addr #KVS_address f).

  Lemma runner_spec :
    {{{
      server_addr ⤳ (∅, ∅) ∗
      client1_addr ⤳ (∅, ∅) ∗
      client2_addr ⤳ (∅, ∅) ∗
      unallocated {[server_addr]} ∗
      unallocated {[client1_addr]} ∗
      unallocated {[client2_addr]} ∗
      free_ip (ip_of_address server_addr) ∗
      free_ip (ip_of_address client1_addr) ∗
      free_ip (ip_of_address client2_addr)
    }}}
      runner @["system"]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(srv_∅ & clt1_∅ & clt2_∅ & srv_unalloc & clt1_unalloc &
            clt2_unalloc & srv_free & clt1_free & clt2_free) HΦ".
    rewrite/runner.
    iMod (SI_init_module _ {[client1_addr; client2_addr]})
           as "(% & % & mem & KVS_Init & Hcc)".
    iPoseProof (big_sepS_insert with "mem") as "(x_mem & mem)"; first done.
    iPoseProof (big_sepS_delete _ _ "y" with "mem") as "(y_mem & _)";
      first set_solver.
    iMod (inv_alloc client_inv_name _ client_inv_def with "[x_mem]") as "#inv".
    { iNext. by iExists _. }
    wp_apply (aneris_wp_socket_interp_alloc_singleton KVS_si with "srv_unalloc").
    iIntros "#KVS_si".
    wp_apply (aneris_wp_start {[80%positive]}).
    iSplitL "srv_free"; first done.
    iDestruct (big_sepS_delete _  _ client1_addr with "Hcc")
      as "(Hcc1 & Hcc)";
    first set_solver.
    iDestruct (big_sepS_delete _  _ client2_addr with "Hcc")
      as "(Hcc2 & Hcc)";
    first set_solver.
    iSplitR "KVS_Init srv_∅"; last first.
    { iIntros "!>free". by wp_apply (server_spec with "[$]"). }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iSplitL "clt1_free"; first done.
    iSplitR "clt1_∅ clt1_unalloc Hcc1"; last first.
    {
      iIntros "!>free".
      by wp_apply (transaction1_client_spec client1_addr with "inv [$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iSplitL "clt2_free"; first done.
    iSplitR "clt2_∅ clt2_unalloc y_mem Hcc2"; last first.
    {
      iIntros "!>free".
      by wp_apply (transaction2_client_spec client2_addr with "inv [] [$]");
        first iApply f_spec_holds.
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
  ; ip_of_address client2_addr ]}.

Definition sa_dom : gset socket_address :=
  {[ server_addr ; client1_addr; client2_addr ]}.

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
  do 2 (iDestruct (unallocated_split with "Hunallocated") as "[Hunallocated ?]";
  [set_solver|]). iFrame.
  do 2 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
  iDestruct "Hhist" as "[Hhist ?]"; iFrame).
  do 2 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
  iDestruct "Hips" as "[Hips ?]"; iFrame).
Qed.
