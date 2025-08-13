From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import inject.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.transactional_consistency.read_committed.specs
  Require Import resources specs.
From aneris.examples.transactional_consistency Require Import state_based_model.
From aneris.examples.transactional_consistency Require Import user_params aux_defs.
From aneris.examples.transactional_consistency.read_committed.examples.trace_proof_of_concept
      Require Import trace_proof_of_concept_code.
From aneris.examples.transactional_consistency
     Require Import code_api.
From aneris.examples.transactional_consistency.read_committed.implication_proof
      Require Import si_implies_rc.
From aneris.examples.transactional_consistency.read_committed.trace Require Import adequacy_trace.
Import ser_inj.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation Require Import
     snapshot_isolation_api_implementation
     instantiation_of_init.
From aneris.examples.transactional_consistency Require Import wrapped_library.
From aneris.examples.transactional_consistency.snapshot_isolation.util Require Import util_proof.
From aneris.examples.transactional_consistency.snapshot_isolation Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params.

(** This is a proof of concept that examples can be used with our trace adequacy theorem, 
    as such the contents of this example has been choosen arbitrarily 
    (for convinience, we use the dirty_read example). *)

Definition server_addr := SocketAddressInet "0.0.0.0" 80.
Definition client_1_addr := SocketAddressInet "0.0.0.1" 80.
Definition client_2_addr := SocketAddressInet "0.0.0.2" 80.

Instance params : User_params :=
{| KVS_address := server_addr;
  KVS_keys := {["x"]};
  KVS_InvName := nroot .@ "kvs_inv";
  KVS_serialization := int_serialization;
  KVS_ser_inj := int_ser_is_ser_injective;
  KVS_ser_inj_alt := int_ser_is_ser_injective_alt
|}.

Definition client_inv_name := nroot.@"clinv".

Section proof_of_code.

  Context `{!anerisG Mdl Σ, !RC_resources Mdl Σ}.

  Definition client_inv_def : iProp Σ := "x" ↦ₖ ∅ .

  Definition client_inv : iProp Σ :=
    inv client_inv_name client_inv_def.

  Local Instance KVS_api : KVS_transaction_api :=  
    KVS_wrapped_api KVS_snapshot_isolation_api_implementation.

  Lemma transaction1_spec :
    ∀ (cst : val) sa,
    RC_client_toolbox -∗
    client_inv -∗
    {{{ ConnectionState cst sa CanStart ∗ IsConnected cst sa }}}
      transaction1 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) #inv %Φ !> (CanStart & #HiC) HΦ".
    rewrite/transaction1.
    wp_pures.
    wp_apply ("Hst" $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; eauto.
    iInv "inv" as ">Hkx" "Hclose".
    unfold client_inv_def.
    iModIntro.
    iExists {[ "x" := ∅ ]}.
    iFrame.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hkx"; first iFrame.
    iIntros "(Hcstate & (Hkx & _) & Hcx & _)".
    iMod ("Hclose" with "[Hkx]") as "_".
    { iNext. iFrame. }
    iModIntro. wp_pures.
    wp_apply ("Hwr" $! _ _  ⊤ _ (SerVal #1) with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _.
    iFrame.
    iIntros "Hcx".
    iModIntro.
    wp_pures.
    iLöb as "IH".
    rewrite /util_code.loop.
    wp_pures.
    iApply ("IH" with "[$][$][$]").
  Qed.

  Lemma transaction2_spec :
    ∀ (cst : val) sa,
      RC_client_toolbox -∗
      client_inv -∗
    {{{ ConnectionState cst sa CanStart ∗ IsConnected cst sa }}}
      transaction2 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) #inv %Φ !> (CanStart & #HiC) HΦ".
    rewrite/transaction2.
    wp_pures.
    wp_apply ("Hst" $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; eauto.
    iInv "inv" as ">Hkx" "Hclose".
    unfold client_inv_def.
    iModIntro.
    iExists {[ "x" := ∅ ]}.
    iFrame.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hkx"; first iFrame.
    iIntros "(Hcstate & (Hkx & _) & Hcx & _)".
    iMod ("Hclose" with "[Hkx]") as "_".
    { iNext. iFrame. }
    iModIntro. wp_pures.
    wp_apply ("Hrd" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][][$][HΦ Hcx Hcstate]"); 
      first solve_ndisj; first set_solver.
    iNext.
    iInv "inv" as ">Hkx" "Hclose".
    iModIntro.
    iExists _, _.
    iFrame.
    iIntros  (wo) "(Hcx & Hkx & Hdisj)".
    iMod ("Hclose" with "[Hkx]") as "_".
    { iNext. iFrame. }
    iModIntro.
    wp_pures.
    iDestruct "Hdisj" as "[(_ & Hdisj) | (%Hfalse & _)]".
    - iDestruct "Hdisj" as "[[%v ( _ & %Hfalse)]|->]".
      + set_solver.
      + rewrite /assert.
        wp_pures.
        wp_apply ("Hcom" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][$]"); first solve_ndisj.
        iInv "inv" as ">Hkx" "Hclose".
        iModIntro.
        iExists (dom {["x" := ∅]}), ({["x" := None]}), ({["x" := ∅]}).
        iFrame.
        iSplitL "Hcx Hkx".
        * iSplitR. iPureIntro. set_solver. 
          iSplitR. iPureIntro. set_solver.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
        * iIntros (b) "(Hstate & Hdisj)".
          iMod ("Hclose" with "[Hdisj]") as "_".
          { 
            iNext. iDestruct "Hdisj" as "[(_ & Hkey)|(_ & Hkey)]".
            - rewrite !big_sepM2_insert; try set_solver.
              simpl. iDestruct "Hkey" as "(Hey & _)". by iFrame.
            - rewrite !big_sepM_insert; try set_solver.
              iDestruct "Hkey" as "(Hey & _)". by iFrame. 
          }
          iModIntro.
          wp_pures.
          by iApply "HΦ". 
    - exfalso.
      by apply Hfalse.
  Qed.

  Lemma transaction1_client_spec :
    ∀ clt,
    client_inv -∗
    RC_client_toolbox -∗
    {{{
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_rc ∗
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
    RC_client_toolbox -∗
    {{{
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_rc ∗
      unallocated {[clt]} ∗
      KVS_ClientCanConnect clt ∗
      free_ports (ip_of_address clt) {[port_of_address clt]}
    }}}
      transaction2_client #clt #KVS_address @[ip_of_address clt]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (clt) "#inv (#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (∅ & #KVS_si & unalloc & Hcc & free) HΦ".
    rewrite/transaction2_client.
    wp_pures.
    wp_apply ("Hinit_cli" with "[$∅ $unalloc $free $KVS_si $Hcc]").
    iIntros (cst) "CanStart".
    wp_pures.
    wp_apply (transaction2_spec with "[] [$inv] [$CanStart]").
    iFrame "#".
    done.
  Qed.

  Lemma server_spec :
    RC_client_toolbox -∗
    {{{
      KVS_Init ∗
      KVS_address ⤳ (∅, ∅) ∗
      free_ports (ip_of_address KVS_address) {[port_of_address KVS_address]} ∗
      KVS_address ⤇ KVS_rc
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

  Context `{!anerisG Mdl Σ, !KVSG Σ}.

  Definition example_runner : expr :=
    let: "serveraddr" := MakeAddress #"0.0.0.0" #80 in
    let: "client1addr" := MakeAddress #"0.0.0.1" #80 in
    let: "client2addr" := MakeAddress #"0.0.0.2" #80 in
    Start "0.0.0.0" (server "serveraddr") ;;
    Start "0.0.0.1" (transaction1_client "client1addr" "serveraddr") ;;
    Start "0.0.0.2" (transaction2_client "client2addr" "serveraddr").

  Lemma example_runner_spec :
    {{{ RC_spec {[server_addr; client_1_addr; client_2_addr]} (KVS_wrapped_api KVS_snapshot_isolation_api_implementation)
      ∗ server_addr ⤳ (∅, ∅)
      ∗ client_1_addr ⤳ (∅, ∅)
      ∗ client_2_addr ⤳ (∅, ∅)
      ∗ unallocated {[server_addr]}
      ∗ unallocated {[client_1_addr]}
      ∗ unallocated {[client_2_addr]}
      ∗ free_ip (ip_of_address server_addr)
      ∗ free_ip (ip_of_address client_1_addr)
      ∗ free_ip (ip_of_address client_2_addr) }}}
      example_runner @["system"]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "(Hlib & Hsrvhist & Hcli1hist & Hcli2hist & Hsrvunalloc & Hcli1unalloc
    & Hcli2unalloc & ? & ? & ?) HΦ".
    iDestruct "Hlib" as (RC_res) "(mem & KVS_Init & #Hginv & Hcc & #specs)".
    iMod (inv_alloc client_inv_name ⊤ (client_inv_def) with "[mem]") as "#Hinv".
    { 
      iNext.
      iDestruct (big_sepS_delete _ _ "x" with "mem") as "(Hx & HKVSres)";
        first set_solver.
      iFrame.
    }
    rewrite /example_runner.
    wp_pures.
    wp_apply (aneris_wp_socket_interp_alloc_singleton KVS_rc with "Hsrvunalloc").
    iIntros "#HKVS_rc".
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iDestruct (big_sepS_delete _  _ client_1_addr with "Hcc")
      as "(Hcc1 & Hcc)";
    first set_solver.
    iDestruct (big_sepS_delete _  _ client_2_addr with "Hcc")
      as "(Hcc2 & Hcc)";
    first set_solver.
    iSplitR "Hsrvhist KVS_Init".
    - iModIntro. wp_pures.
      wp_apply (aneris_wp_start {[80%positive : port]}).
      iFrame.
      iSplitR "Hcli1hist Hcli1unalloc Hcc1".
      + iModIntro. wp_pures.
        wp_apply (aneris_wp_start {[80%positive : port]}).
        iFrame.
        iSplitR "Hcli2hist Hcli2unalloc Hcc2".
        * by iApply "HΦ".
        * iIntros "!> Hports".
          by wp_apply (transaction2_client_spec client_2_addr with "[$] [$] [$]").
      + iIntros "!> Hports".
        by wp_apply (transaction1_client_spec client_1_addr with "[$] [$] [$]").
    - iIntros "!> Hports". wp_apply (server_spec with "[$][$]"); done.
  Qed.

End proof_of_runner.

Definition ips : gset ip_address :=
  {[ ip_of_address server_addr ; ip_of_address client_1_addr
  ; ip_of_address client_2_addr ]}.

Definition sa_dom : gset socket_address :=
  {[ server_addr ; client_1_addr; client_2_addr ]}.

Definition init_state :=
  {|
    state_heaps := {["system" := ∅ ]};
    state_sockets := {["system" := ∅ ]};
    state_ms := ∅;
    state_trace := [];
  |}.

Theorem trace_valid :
  ∀ σ' t,
    rtc step ([(mkExpr "system" example_runner)], init_state) (t, σ') →
    valid_trace_rc (state_trace σ').
Proof.
  intros.
  set (Σ := #[anerisΣ adequacy_no_model.unit_model; KVSΣ]).
  eapply (@adequacy_trace_rc Σ _ _ _ _ init_state _ _ 
    {[server_addr; client_1_addr; client_2_addr]} ips); try done.
  - iIntros (Ag).
    assert (specs.SI_init) as SI_init; first apply _.
    apply implication_si_rc in SI_init.
    iMod (@RC_init_module _ _ _ _ KVS_snapshot_isolation_api_implementation 
      _ _ {[server_addr; client_1_addr; client_2_addr]}) 
      as "RC_spec";
      first solve_ndisj.
    iModIntro.
    iFrame.
  - iIntros.
    iIntros (Φ) "!# (Hlib & Hunalloc & Hmes & Hfree) HΦ".
    iApply (@example_runner_spec adequacy_no_model.unit_model Σ anerisG0 with 
      "[$Hlib Hunalloc Hmes Hfree]"); last done.
    do 2 (iDestruct (unallocated_split with "Hunalloc") as "[Hunalloc ?]";
      [set_solver|]); iFrame.
    do 2 (rewrite big_sepS_union; [|set_solver];
    rewrite !big_sepS_singleton;
    iDestruct "Hmes" as "[Hmes ?]"; iFrame).
    do 2 (rewrite big_sepS_union; [|set_solver];
    rewrite !big_sepS_singleton;
    iDestruct "Hfree" as "[Hfree ?]"; iFrame).
Qed.
