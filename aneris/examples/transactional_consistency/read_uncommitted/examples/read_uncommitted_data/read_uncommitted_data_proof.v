From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import inject.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.transactional_consistency.read_uncommitted.specs
  Require Import resources specs.
From aneris.examples.transactional_consistency Require Import user_params aux_defs.
From aneris.examples.transactional_consistency.read_uncommitted.examples.read_uncommitted_data
      Require Import read_uncommitted_data_code.
From aneris.examples.transactional_consistency.read_committed.implication_proof
      Require Import si_implies_rc.
From aneris.examples.transactional_consistency.read_uncommitted.implication_proof
      Require Import rc_implies_ru.
Import ser_inj.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation Require Import
     snapshot_isolation_api_implementation
     instantiation_of_init.
From aneris.examples.transactional_consistency.snapshot_isolation.util Require Import util_proof.
From aneris.examples.transactional_consistency.snapshot_isolation Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params.

Definition server_addr := SocketAddressInet "0.0.0.0" 80.
Definition client_1_addr := SocketAddressInet "0.0.0.1" 80.
Definition client_2_addr := SocketAddressInet "0.0.0.2" 80.

Instance params : User_params :=
{| KVS_address := server_addr;
  KVS_keys := {["x"]};
  KVS_InvName := nroot .@ "siinv";
  KVS_serialization := int_serialization;
  KVS_ser_inj := int_ser_is_ser_injective;
  KVS_ser_inj_alt := int_ser_is_ser_injective_alt
|}.

Definition client_inv_name := nroot.@"clinv".

Section proof_of_code.

  Context `{!anerisG Mdl Σ, !RU_resources Mdl Σ}.

  Definition client_inv_def : iProp Σ :=
    ∃ V, "x" ↦ₖ V ∗ (⌜V = ∅ ⌝ ∨ ⌜V = {[(#1)]}⌝).

  Definition client_inv : iProp Σ :=
    inv client_inv_name client_inv_def.

  Lemma transaction1_spec :
    ∀ (cst : val) sa,
    RU_client_toolbox -∗
    client_inv -∗
    {{{ ConnectionState cst sa CanStart ∗ IsConnected cst sa }}}
      transaction1 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) #inv %Φ !> (CanStart & #HiC) HΦ".
    rewrite/transaction1.
    wp_pures.
    wp_apply ("Hst" $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; eauto.
    iInv "inv" as ">(%V & Hkx & Hdisj)" "Hclose".
    unfold client_inv_def.
    iModIntro.
    iExists {[ "x" := V ]}.
    iFrame.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hkx"; first iFrame.
    iNext. iIntros "(Hcstate & (Hkx & _) & Hcx & _)".
    iMod ("Hclose" with "[Hkx Hdisj]") as "_".
    { iNext. iExists _. iFrame. }
    iModIntro. wp_pures.
    wp_apply ("Hwr" $! _ _  (⊤ ∖ ↑client_inv_name) _ (SerVal #1) with "[][][$][HΦ Hcx Hcstate]"); 
      first solve_ndisj; first set_solver.
    iInv "inv" as ">(%V' & Hkx & Hdisj)" "Hclose".
    iModIntro.
    iExists _, _.
    iFrame.
    iNext.
    iIntros  "(Hcx & Hkx)".
    iMod ("Hclose" with "[Hkx Hdisj]") as "_".
    { 
      iNext. iExists {[#1]}.
      iDestruct "Hdisj" as "[-> | ->]".
      - simpl.
        assert (∅ ∪ {[#1]} = {[#1]}) as ->; first set_solver.
        iFrame.
        by iRight.
      - simpl.
        assert ({[#1; #1]} = {[#1]}) as ->; first set_solver.
        iFrame.
        by iRight.
    }
    iModIntro.
    wp_pures.
    iLöb as "IH".
    rewrite /util_code.loop.
    wp_pures.
    iApply ("IH" with "[$][$][$]").
  Qed.

  Lemma transaction2_spec :
    ∀ (cst : val) sa,
      RU_client_toolbox -∗
      client_inv -∗
    {{{ ConnectionState cst sa CanStart ∗ IsConnected cst sa }}}
      transaction2 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) #inv %Φ !> (CanStart & #HiC) HΦ".
    rewrite/transaction2.
    wp_pures.
    wp_apply ("Hst" $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; eauto.
    iInv "inv" as ">(%V & Hkx & Hdisj)" "Hclose".
    unfold client_inv_def.
    iModIntro.
    iExists {[ "x" := V ]}.
    iFrame.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hkx"; first iFrame.
    iNext. iIntros "(Hcstate & (Hkx & _) & Hcx & _)".
    iMod ("Hclose" with "[Hkx Hdisj]") as "_".
    { iNext. iExists _. iFrame. }
    iModIntro. wp_pures.
    wp_apply ("Hrd" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][][$][HΦ Hcx Hcstate]"); 
      first solve_ndisj; first set_solver.
    iInv "inv" as ">(%V' & Hkx & %Hdisj)" "Hclose".
    iModIntro.
    iExists _, _.
    iFrame.
    iNext.
    iIntros  (wo) "(Hcx & Hkx & Hdisj')".
    iMod ("Hclose" with "[Hkx]") as "_".
    { iNext. iExists _. iFrame. by iPureIntro. }
    iModIntro.
    wp_pures.
    destruct Hdisj as [-> | ->].
    - iDestruct "Hdisj'" as "[(_ & [%Hfalse | ->]) | (%Hfalse & _)]"; first set_solver.
      + rewrite /assert. 
        wp_pures.
        rewrite /util_code.commitU.
        wp_pures.
        wp_apply ("Hcom" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][$]"); first solve_ndisj.
        iInv "inv" as ">(%V' & Hkx & %Hdisj)" "Hclose".
        iModIntro.
        iExists (dom {["x" := V]}), ({["x" := None]}), ({["x" := V']}).
        iFrame.
        iSplitL "Hcx Hkx".
        * iSplitR. iPureIntro. set_solver. 
          iSplitR. iPureIntro. set_solver.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
        * iNext.
          iIntros (b) "(Hstate & Hkeys)".
          iMod ("Hclose" with "[Hkeys]") as "_".
          { 
            iNext. iExists _.
            rewrite !big_sepM_insert; try set_solver.
            iDestruct "Hkeys" as "(Hkeys & _)". by iFrame. 
          }
          iModIntro.
          wp_pures.
          by iApply "HΦ".
      + exfalso.
        by apply Hfalse.
    - iDestruct "Hdisj'" as "[(_ & [(%v & -> & %Hin) | ->]) | (%Hfalse & sdfsd)]".
      + rewrite /assert. 
        wp_pures.
        assert (v = #1) as ->; first set_solver.
        wp_pures.
        rewrite /util_code.commitU.
        wp_pures.
        wp_apply ("Hcom" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][$]"); first solve_ndisj.
        iInv "inv" as ">(%V' & Hkx & %Hdisj)" "Hclose".
        iModIntro.
        iExists (dom {["x" := V]}), ({["x" := None]}), ({["x" := V']}).
        iFrame.
        iSplitL "Hcx Hkx".
        * iSplitR. iPureIntro. set_solver. 
          iSplitR. iPureIntro. set_solver.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
        * iNext.
          iIntros (b) "(Hstate & Hkeys)".
          iMod ("Hclose" with "[Hkeys]") as "_".
          { 
            iNext. iExists _.
            rewrite !big_sepM_insert; try set_solver.
            iDestruct "Hkeys" as "(Hkeys & _)". by iFrame. 
          }
          iModIntro.
          wp_pures.
          by iApply "HΦ".
      + rewrite /assert. 
        wp_pures.
        rewrite /util_code.commitU.
        wp_pures.
        wp_apply ("Hcom" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][$]"); first solve_ndisj.
        iInv "inv" as ">(%V' & Hkx & %Hdisj)" "Hclose".
        iModIntro.
        iExists (dom {["x" := V]}), ({["x" := None]}), ({["x" := V']}).
        iFrame.
        iSplitL "Hcx Hkx".
        * iSplitR. iPureIntro. set_solver. 
          iSplitR. iPureIntro. set_solver.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
        * iNext.
          iIntros (b) "(Hstate & Hkeys)".
          iMod ("Hclose" with "[Hkeys]") as "_".
          { 
            iNext. iExists _.
            rewrite !big_sepM_insert; try set_solver.
            iDestruct "Hkeys" as "(Hkeys & _)". by iFrame. 
          }
          iModIntro.
          wp_pures.
          by iApply "HΦ".
      + exfalso.
        by apply Hfalse.
  Qed.

  Lemma transaction1_client_spec :
    ∀ clt,
    client_inv -∗
    RU_client_toolbox -∗
    {{{
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_ru ∗
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
    RU_client_toolbox -∗
    {{{
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_ru ∗
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
    RU_client_toolbox -∗
    {{{
      KVS_Init ∗
      KVS_address ⤳ (∅, ∅) ∗
      free_ports (ip_of_address KVS_address) {[port_of_address KVS_address]} ∗
      KVS_address ⤇ KVS_ru
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

  Context `{!anerisG Mdl Σ, !RU_init, !KVSG Σ}.

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
      ∗ free_ip (ip_of_address client_2_addr) }}}
      example_runner @["system"]
    {{{ v, RET v; True }}}.
  Proof.
    iMod (RU_init_module _ {[client_1_addr; client_2_addr]})
      as (RU_res) "(mem & KVS_Init & #Hginv & Hcc & #specs)";
         first done.
    iMod (inv_alloc client_inv_name ⊤ (client_inv_def) with "[mem]") as "#Hinv".
    { 
      iNext.
      iDestruct (big_sepS_delete _ _ "x" with "mem") as "(Hx & HKVSres)";
        first set_solver.
      iExists _.
      iFrame. by iLeft.
    }
    iIntros (Φ) "(Hsrvhist & Hcli1hist & Hcli2hist & Hsrvunalloc & Hcli1unalloc
    & Hcli2unalloc & ? & ? & ?) HΦ".
    rewrite /example_runner.
    wp_pures.
    wp_apply (aneris_wp_socket_interp_alloc_singleton KVS_ru with "Hsrvunalloc").
    iIntros "#HKVS_ru".
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

Definition unit_model := model _ (λ _ _, False) ().

Lemma unit_model_rel_finitary : aneris_model_rel_finitary unit_model.
Proof. intros ?. apply finite_smaller_card_nat. apply _. Qed.

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
  |}.

Theorem runner_safe :
  aneris_adequate example_runner "system" init_state (λ _, True).
Proof.
  set (Σ := #[anerisΣ unit_model; KVSΣ]).
  apply (@adequacy Σ unit_model _ _ ips sa_dom ∅ ∅ ∅);
    [apply unit_model_rel_finitary|move=>?|set_solver..].
  iIntros "!> Hunallocated Hhist Hfrag Hips Hlbl _ _ _ _".
  iApply (example_runner_spec with "[Hunallocated Hhist Hfrag Hips Hlbl]" ).
  2 : { iModIntro. done. }
  do 2 (iDestruct (unallocated_split with "Hunallocated") as "[Hunallocated ?]";
  [set_solver|]). iFrame.
  do 2 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
  iDestruct "Hhist" as "[Hhist ?]"; iFrame).
  do 2 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
  iDestruct "Hips" as "[Hips ?]"; iFrame).
  Unshelve.
  apply implication_rc_ru.
  apply implication_si_rc.
  apply _.
Qed.