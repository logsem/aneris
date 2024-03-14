(* From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  time events aux_defs resources specs.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.transactional_consistency.snapshot_isolation.examples.disjoint_writes
  Require Import disjoint_writes_code.
Import ser_inj.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation Require Import
     snapshot_isolation_api_implementation
     instantiation_of_init.
From aneris.examples.transactional_consistency.snapshot_isolation.util Require Import util_proof.
From iris.algebra Require Import excl.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params.

Definition server_addr := SocketAddressInet "0.0.0.0" 80.
Definition client_1_addr := SocketAddressInet "0.0.0.1" 80.
Definition client_2_addr := SocketAddressInet "0.0.0.2" 80.

Instance params : User_params :=
{| KVS_address := server_addr;
  KVS_keys := {["x"; "y"]};
  KVS_InvName := nroot .@ "siinv";
  KVS_serialization := int_serialization;
  KVS_ser_inj := int_ser_is_ser_injective;
  KVS_ser_inj_alt := int_ser_is_ser_injective_alt
|}.

Section proofs.

Context `{!anerisG Mdl Σ, !SI_resources Mdl Σ, !SI_client_toolbox, !KVSG Σ}.

  Lemma server_spec ip port :
    ip = ip_of_address KVS_address →
    port = port_of_address KVS_address →
    {{{ KVS_Init
      ∗ KVS_address ⤳ (∅, ∅)
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
    server #KVS_address @[ip]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Hip Hports Φ) "(? & ? & ? & ?) HΦ".
    rewrite /server. wp_pures. rewrite Hip Hports.
    by wp_apply (SI_init_kvs_spec with "[$]").
  Qed.

  Lemma transaction1_spec :
    ∀ cst sa h,
    {{{
      ConnectionState cst sa CanStart ∗
      IsConnected cst sa ∗
      "x" ↦ₖ h
    }}}
      transaction1 cst @[ip_of_address sa]
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros (cst sa h Φ) "(CanStart & #HiC & x_h) HΦ".
    rewrite/transaction1.
    wp_pures.
    inversion H.
    wp_apply (SI_start_spec _ _ ⊤); first done; eauto.
    iModIntro.
    iExists {[ "x" := h ]}.
    iFrame.
    iSplitL "x_h"; first by iApply big_sepM_insert; first done; iFrame.
    iIntros "!>(Active & mem & cache & _)".
    iPoseProof (big_sepM_insert with "cache") as
      "((x_h & x_upd) & _)"; first done.
    iModIntro.
    wp_pures.
    wp_apply (SI_write_spec _ _ _ _ (SerVal #1) with "[][$] [$x_h $x_upd $HiC]"); first done.
    iIntros "(x_1 & x_upd)".
    wp_pures.
    wp_apply (commitT_spec _ _ ⊤ with "[//]"); eauto.
    iModIntro.
    iExists _, _, {[ "x" := (Some #1, true) ]}.
    iFrame.
    iSplitL "x_1 x_upd".
    {
      iSplit.
      {
        iPureIntro.
        rewrite bool_decide_spec=>k k_key.
        case eq: ("x" =? k)%string.
        { apply String.eqb_eq in eq.
          by rewrite -eq !lookup_insert bool_decide_true. }
        apply eqb_neq in eq.
        by rewrite (proj2 (lookup_insert_None _ _ _ _)).
      }
      rewrite !dom_insert_L !dom_empty_L.
      do 2 (iSplit; first done).
      iApply big_sepM_insert; first done.
      by iFrame.
    }
    iIntros "!>_".
    by iApply "HΦ".
  Qed.

  Lemma transaction2_spec :
    ∀ cst sa h,
    {{{
      ConnectionState cst sa CanStart ∗
      IsConnected cst sa ∗
      "y" ↦ₖ h
    }}}
      transaction2 cst @[ip_of_address sa]
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros (cst sa h Φ) "(CanStart & #HiC & y_h) HΦ".
    rewrite/transaction2.
    wp_pures.
    wp_apply (SI_start_spec _ _ ⊤); first done; eauto.
    iModIntro.
    iExists {[ "y" := h ]}.
    iFrame.
    iSplitL "y_h"; first by iApply big_sepM_insert; first done; iFrame.
    iIntros "!>(Active & mem & cache & _)".
    iPoseProof (big_sepM_insert with "cache") as
      "((y_h & y_upd) & _)"; first done.
    iModIntro.
    wp_pures.
    wp_apply (SI_write_spec _ _ _ _ (SerVal #1) with "[][$][$y_h $y_upd $HiC]"); eauto.
    iIntros "(y_1 & y_upd)".
    wp_pures.
    wp_apply (commitT_spec _ _ ⊤ with "[//][$]").
    iModIntro.
    iExists _, _, {[ "y" := (Some #1, true) ]}.
    iFrame.
    iSplitL "y_1 y_upd".
    {
      iSplit.
      {
        iPureIntro.
        rewrite bool_decide_spec=>k k_key.
        case eq: ("y" =? k)%string.
        { apply String.eqb_eq in eq.
          by rewrite -eq !lookup_insert bool_decide_true. }
        apply eqb_neq in eq.
        by rewrite (proj2 (lookup_insert_None _ _ _ _)).
      }
      rewrite !dom_insert_L !dom_empty_L.
      do 2 (iSplit; first done).
      iApply big_sepM_insert; first done.
      by iFrame.
    }
    iIntros "!>_".
    by iApply "HΦ".
  Qed.

  Lemma transaction1_client_spec :
    ∀ sa h,
    {{{
      sa ⤳ (∅, ∅) ∗
      unallocated {[sa]} ∗
      KVS_ClientCanConnect sa ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      KVS_address ⤇ KVS_si ∗
      "x" ↦ₖ h
    }}}
      transaction1_client $sa $KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (sa h Φ) "(∅ & unalloc & Hcc & free & #KVS_si & x_h) HΦ".
    rewrite/transaction1_client.
    wp_pures.
    wp_apply (SI_init_client_proxy_spec with "[$]").
    iIntros (cst) "(CanStart & #HiC)".
    wp_pures.
    by wp_apply (transaction1_spec with "[$]").
  Qed.

  Lemma transaction2_client_spec :
    ∀ sa h,
    {{{
      sa ⤳ (∅, ∅) ∗
      unallocated {[sa]} ∗
      KVS_ClientCanConnect sa ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      KVS_address ⤇ KVS_si ∗
      "y" ↦ₖ h
    }}}
      transaction2_client $sa $KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (sa h Φ) "(∅ & unalloc & free & Hcc & #KVS_si & y_h) HΦ".
    rewrite/transaction2_client.
    wp_pures.
    wp_apply (SI_init_client_proxy_spec with "[$]").
    iIntros (cst) "(CanStart & #HiC)".
    wp_pures.
    by wp_apply (transaction2_spec with "[$]").
  Qed.

End proofs.

Section proof_runner.

Context `{!anerisG Mdl Σ, !SI_init, !KVSG Σ}.

  Definition example_runner : expr :=
    let: "serveraddr" := MakeAddress #"0.0.0.0" #80 in
    let: "client1addr" := MakeAddress #"0.0.0.1" #80 in
    let: "client2addr" := MakeAddress #"0.0.0.2" #80 in
    Start "0.0.0.0" (server "serveraddr") ;;
    Start "0.0.0.1" (transaction1_client "client1addr" "serveraddr") ;;
    Start "0.0.0.2" (transaction2_client "client2addr" "serveraddr").

  Lemma example_runner_spec :
    {{{ server_addr ⤳ (∅, ∅)
      ∗ client_1_addr ⤳ (∅, ∅)
      ∗ client_2_addr ⤳ (∅, ∅)
      ∗ unallocated {[server_addr]}
      ∗ unallocated {[client_1_addr]}
      ∗ unallocated {[client_2_addr]}
      ∗ free_ip (ip_of_address server_addr)
      ∗ free_ip (ip_of_address client_1_addr)
      ∗ free_ip (ip_of_address client_2_addr)
     }}}
      example_runner @["system"]
    {{{ RET #(); True }}}.
  Proof.
    iMod (SI_init_module _ {[client_1_addr; client_2_addr]})
      as (SI_res) "(mem & KVS_Init & #Hginv & Hcc & %specs)";
      first done.
    destruct specs as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6).
    iPoseProof (big_sepS_insert with "mem") as "(mem_x & mem)"; first set_solver.
    iPoseProof (big_sepS_delete _ _ "y" with "mem") as "(mem_y & _)"; first done.
    iIntros (Φ) "(srv_∅ & clt1_∅ & clt2_∅ & srv_unalloc & clt1_unalloc &
      clt2_unalloc & ? & ? & ?) HΦ".
    rewrite /example_runner.
    wp_pures.
    wp_apply (aneris_wp_socket_interp_alloc_singleton KVS_si with "srv_unalloc").
    iIntros "#KVS_si".
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "srv_∅ KVS_Init".
    iDestruct (big_sepS_delete _  _ client_1_addr with "Hcc")
      as "(Hcc1 & Hcc)";
      first set_solver.
    iDestruct (big_sepS_delete _  _ client_2_addr with "Hcc")
      as "(Hcc2 & Hcc)";
      first set_solver.
    - iModIntro. wp_pures.
      wp_apply (aneris_wp_start {[80%positive : port]}).
      iFrame.
      iSplitR "clt1_∅ clt1_unalloc mem_x Hcc1".
      + iModIntro. wp_pures.
        wp_apply (aneris_wp_start {[80%positive : port]}).
        iFrame.
        iSplitR "clt2_∅ clt2_unalloc mem_y Hcc2".
        * by iApply "HΦ".
        * iIntros "!> Hports".
          by wp_apply (transaction2_client_spec client_2_addr with "[$]").
      + iIntros "!> Hports".
        by wp_apply (transaction1_client_spec client_1_addr with "[$]").
    - iIntros "!> Hports". by wp_apply (server_spec with "[$]").
      Unshelve. all: by eauto.
  Qed.

End proof_runner.

Definition unit_model := model _ (λ _ _, False) ().
Lemma unit_model_rel_finitary : aneris_model_rel_finitary unit_model.
Proof. intros ?. apply finite_smaller_card_nat. apply _. Qed.

Definition ips : gset string :=
  {[ ip_of_address server_addr ; ip_of_address client_1_addr
  ; ip_of_address client_2_addr ]}.

Definition sa_dom : gset socket_address :=
  {[ server_addr ; client_1_addr; client_2_addr ]}.

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
  Unshelve.
  do 2 (iDestruct (unallocated_split with "Hunallocated") as "[Hunallocated ?]";
  [set_solver|]). iFrame.
  do 2 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
  iDestruct "Hhist" as "[Hhist ?]"; iFrame).
  do 2 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
        iDestruct "Hips" as "[Hips ?]"; iFrame).
Qed. *)
