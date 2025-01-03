(* From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  time events aux_defs resources specs.
From aneris.examples.transactional_consistency.snapshot_isolation.examples.disjoint_reads
      Require Import disjoint_reads_code.
Import ser_inj.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation Require Import
     snapshot_isolation_api_implementation
     instantiation_of_init.
From aneris.examples.transactional_consistency.snapshot_isolation.util Require Import util_proof.
From iris.algebra Require Import excl.
From aneris.examples.transactional_consistency.snapshot_isolation.examples Require Import proof_resources.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params.

Definition server_addr := SocketAddressInet "0.0.0.0" 80.
Definition client_1_addr := SocketAddressInet "0.0.0.1" 80.
Definition client_2_addr := SocketAddressInet "0.0.0.2" 80.
Definition client_3_addr := SocketAddressInet "0.0.0.3" 80.

Instance params : User_params :=
{| KVS_address := server_addr;
  KVS_keys := {["x"; "y"]};
  KVS_InvName := nroot .@ "siinv";
  KVS_serialization := int_serialization;
  KVS_ser_inj := int_ser_is_ser_injective;
  KVS_ser_inj_alt := int_ser_is_ser_injective_alt
|}.

Definition client_inv_name := nroot.@"clinv".

Section proofs.

Context `{!anerisG Mdl Σ, !SI_resources Mdl Σ, !SI_client_toolbox, !KVSG Σ}.

  Definition client_inv γx γy : iProp Σ :=
    ("x" ↦ₖ [] ∨ (token γx ∗ "x" ↦ₖ [ #1])) ∗ ("y" ↦ₖ [] ∨ (token γy ∗ "y" ↦ₖ [ #2])).

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

  Lemma client_1_spec ip port γx γy :
    ip = ip_of_address client_1_addr →
    port = port_of_address client_1_addr →
    {{{ inv client_inv_name (client_inv γx γy)
      ∗ token γx
      ∗ client_1_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_1_addr]}
      ∗ KVS_ClientCanConnect client_1_addr
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      transaction1_client $client_1_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Heqip Heqport Φ) "(#Hinv & Fx & Hmsghis & Hunalloc
        & Hcc & Hports & Hprot) HΦ" .
    rewrite /transaction1_client. wp_pures. rewrite Heqip Heqport.
    wp_apply (SI_init_client_proxy_spec
               with "[$Hunalloc $Hprot $Hmsghis $Hports $Hcc]").
    iIntros (rpc) "(Hcstate & #HiC)".
    wp_pures. rewrite /transaction1. wp_pures.
    wp_apply (SI_start_spec rpc client_1_addr (⊤ ∖ ↑client_inv_name)); try solve_ndisj.
    iInv (client_inv_name) as ">([Hx|(abs & _)] & Hy)" "HClose";
      last by iCombine "Fx abs" gives "%abs".
    iModIntro. iFrame.
    iExists {["x" := []]}.
    rewrite !big_sepM_insert; [|set_solver..].
    rewrite big_sepM_empty.
    iSplitL "Hx"; first iFrame.
    iNext. iIntros "(Hcstate & [Hkx _] & [Hcx _] & _)".
    iMod ("HClose" with "[Hkx Hy]") as "_"; first iFrame.
    iModIntro. wp_pures.
    wp_apply (SI_write_spec  _ _ _ _ (SerVal #1) with "[][$][Hcx]").
    set_solver. iFrame. iIntros "Hcx". wp_pures.
    wp_apply (commitT_spec rpc client_1_addr (⊤ ∖ ↑client_inv_name));
      try solve_ndisj.
    iInv (client_inv_name) as ">([Hx|(abs & _)] & Hy)" "HClose";
      last by iCombine "Fx abs" gives "%abs".
    iModIntro.
    iExists {["x" := []]}, _, {["x" := (Some #1, true)]}.
    iFrame. iSplitL "Hcx Hx".
    - iSplit; first done.
      iSplit; first by rewrite !dom_singleton_L.
      iSplitL "Hx"; first by rewrite big_sepM_singleton.
      rewrite big_sepM_singleton.
      iFrame.
    - iNext. rewrite big_sepM2_singleton/=.
      iIntros "(_ & Hx & _)".
      iMod ("HClose" with "[Fx Hx Hy]") as "_"; last by iApply "HΦ".
      iNext. iFrame. iRight. iFrame.
  Qed.

  Lemma client_2_spec ip port γx γy :
    ip = ip_of_address client_2_addr →
    port = port_of_address client_2_addr →
    {{{ inv client_inv_name (client_inv γx γy)
      ∗ token γy
      ∗ client_2_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_2_addr]}
      ∗ KVS_ClientCanConnect client_2_addr
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      transaction2_client $client_2_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Heqip Heqport Φ) "(#Hinv & Fy & Hmsghis & Hunalloc
        & Hcc & Hports & Hprot) HΦ" .
    rewrite /transaction2_client. wp_pures. rewrite Heqip Heqport.
    wp_apply (SI_init_client_proxy_spec
               with "[$Hunalloc $Hprot $Hmsghis $Hports $Hcc]").
    iIntros (rpc) "(Hcstate & #HiC)".
    wp_pures. rewrite /transaction2. wp_pures.
    wp_apply (SI_start_spec rpc client_2_addr (⊤ ∖ ↑client_inv_name)); try solve_ndisj.
    iInv (client_inv_name) as ">(Hx & [Hy|(abs & _)])" "HClose";
      last by iCombine "Fy abs" gives "%abs".
    iModIntro. iFrame.
    iExists {["y" := []]}.
    rewrite !big_sepM_insert; [|set_solver..].
    rewrite big_sepM_empty.
    iSplitL "Hy"; first iFrame.
    iNext. iIntros "(Hcstate & [Hky _] & [Hcy _] & _)".
    iMod ("HClose" with "[Hky Hx]") as "_"; first iFrame.
    iModIntro. wp_pures.
    wp_apply (SI_write_spec  _ _ _ _ (SerVal #2) with "[][$][Hcy]").
    set_solver. iFrame. iIntros "Hcy". wp_pures.
    wp_apply (commitT_spec rpc client_2_addr (⊤ ∖ ↑client_inv_name));
      try solve_ndisj.
    iInv (client_inv_name) as ">(Hx & [Hy|(abs & _)])" "HClose";
      last by iCombine "Fy abs" gives "%abs".
    iModIntro.
    iExists {["y" := []]}, _, {["y" := (Some #2, true)]}.
    iFrame. iSplitL "Hcy Hy".
    - iSplit; first done.
      iSplit; first by rewrite !dom_singleton_L.
      iSplitL "Hy"; first by rewrite big_sepM_singleton.
      rewrite big_sepM_singleton.
      iFrame.
    - iNext. rewrite big_sepM2_singleton/=.
      iIntros "(_ & Hy & _)".
      iMod ("HClose" with "[Fy Hx Hy]") as "_"; last by iApply "HΦ".
      iNext. iFrame. iRight. iFrame.
  Qed.

  Lemma client_3_spec ip port client_3_addr γx γy :
    ip = ip_of_address client_3_addr →
    port = port_of_address client_3_addr →
    {{{ inv client_inv_name (client_inv γx γy)
      ∗ client_3_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_3_addr]}
      ∗ KVS_ClientCanConnect client_3_addr
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      transaction3_client $client_3_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Heqip Heqports Φ)
            "(#Hinv & Hmsghis & Hunalloc & Hports & Hcc & Hprot) HΦ" .
    rewrite /transaction3_client. wp_pures. rewrite Heqip Heqports.
    wp_apply (SI_init_client_proxy_spec
               with "[$Hunalloc $Hprot $Hmsghis $Hports $Hcc]").
    iIntros (rpc) "(Hcstate & #HiC)". wp_pures. rewrite /transaction3. wp_pures.
    wp_apply (SI_start_spec rpc client_3_addr (⊤ ∖ ↑client_inv_name));
    try solve_ndisj.
    iInv (client_inv_name) as ">[Hx Hy]" "HClose".
    iAssert (∃ hx hy, "x" ↦ₖ hx ∗ "y" ↦ₖ hy ∗
        ▷ ("x" ↦ₖ hx ∗ "y" ↦ₖ hy ={⊤ ∖ ↑client_inv_name,⊤}=∗ emp))%I with
          "[Hx Hy HClose]" as "(%hx & %hy & Hx & Hy & HClose)".
    { iDestruct "Hx" as "[Hx|[Fx Hx]]"; iDestruct "Hy" as "[Hy|[Fy Hy]]";
        iExists _, _; iFrame; iIntros "!>(Hx & Hy)".
      - iMod ("HClose" with "[Hx Hy]") as "_"; last done.
        iFrame.
      - iMod ("HClose" with "[Hx Hy Fy]") as "_"; last done.
        iFrame. iRight. iFrame.
      - iMod ("HClose" with "[Hx Fx Hy]") as "_"; last done.
        iFrame. iRight. iFrame.
      - iMod ("HClose" with "[Hx Fx Hy Fy]") as "_"; last done.
        iSplitL "Hx Fx"; iRight; iFrame.
    }
    iModIntro. iFrame.
    iExists {["x" := hx; "y" := hy]}.
    rewrite !big_sepM_insert; [|set_solver..].
    rewrite !big_sepM_empty.
    iSplitL "Hy Hx"; first iFrame.
    iNext.
    iIntros "(Hcstate & [Hkx [Hky _]] & ((Hcx & Hsx) & (Hcy & Hsy) & _) & _)".
    iMod ("HClose" with "[Hkx Hky]") as "_"; first by iFrame.
    iModIntro.
    wp_pures.
    wp_apply (SI_read_spec _ _ _ _ with "[][$][Hcx]"); [set_solver|iFrame|].
    iIntros "Hcx".
    wp_pures.
    wp_apply (SI_read_spec _ _ _ _ with "[][$][Hcy]"); [set_solver|iFrame|].
    iIntros "Hcy".
    wp_pures.
    wp_apply (commitT_spec rpc client_3_addr (⊤ ∖ ↑client_inv_name) with "[] [$]");
      first solve_ndisj.
    iInv (client_inv_name) as ">[Hx Hy]" "HClose".
    iAssert (∃ hx hy, "x" ↦ₖ hx ∗ "y" ↦ₖ hy ∗
        ▷ ("x" ↦ₖ hx ∗ "y" ↦ₖ hy ={⊤ ∖ ↑client_inv_name,⊤}=∗ emp))%I with
          "[Hx Hy HClose]" as "(%hx' & %hy' & Hx & Hy & HClose)".
    { iDestruct "Hx" as "[Hx|[Fx Hx]]"; iDestruct "Hy" as "[Hy|[Fy Hy]]";
        iExists _, _; iFrame; iIntros "!>(Hx & Hy)".
      - iMod ("HClose" with "[Hx Hy]") as "_"; last done.
        iFrame.
      - iMod ("HClose" with "[Hx Hy Fy]") as "_"; last done.
        iFrame. iRight. iFrame.
      - iMod ("HClose" with "[Hx Fx Hy]") as "_"; last done.
        iFrame. iRight. iFrame.
      - iMod ("HClose" with "[Hx Fx Hy Fy]") as "_"; last done.
        iSplitL "Hx Fx"; iRight; iFrame.
    }
    iModIntro.
    iExists {["x" := hx'; "y" := hy']}, _,
      {["x" := (last hx, false); "y" := (last hy, false)]}.
    iSplitL "Hcstate Hsx Hsy Hcx Hcy Hx Hy".
    - iFrame.
      iSplit; first by rewrite !dom_insert_L dom_empty_L.
      iSplit; first by rewrite !dom_insert_L !dom_empty_L.
      rewrite !big_sepM_insert// !big_sepM_empty.
      iFrame.
    - rewrite !big_sepM2_insert// big_sepM2_empty.
      iIntros "!>(_ & [Hx _] & [Hy _] & _)".
      replace (commit_event _ hx') with hx'; last by case (last hx).
      replace (commit_event _ hy') with hy'; last by case (last hy).
      iMod ("HClose" with "[Hx Hy]") as "_"; last by iApply "HΦ".
      iFrame.
Qed.

End proofs.

Section proof_runner.

Context `{!anerisG Mdl Σ, !SI_init, !KVSG Σ}.

  Definition example_runner : expr :=
    let: "serveraddr" := MakeAddress #"0.0.0.0" #80 in
    let: "client1addr" := MakeAddress #"0.0.0.1" #80 in
    let: "client2addr" := MakeAddress #"0.0.0.2" #80 in
    let: "client3addr" := MakeAddress #"0.0.0.3" #80 in
    Start "0.0.0.0" (server "serveraddr") ;;
    Start "0.0.0.1" (transaction1_client "client1addr" "serveraddr") ;;
    Start "0.0.0.2" (transaction2_client"client2addr" "serveraddr") ;;
    Start "0.0.0.3" (transaction3_client "client3addr" "serveraddr").

  Lemma example_runner_spec :
    {{{ server_addr ⤳ (∅, ∅)
      ∗ client_1_addr ⤳ (∅, ∅)
      ∗ client_2_addr ⤳ (∅, ∅)
      ∗ client_3_addr ⤳ (∅, ∅)
      ∗ unallocated {[server_addr]}
      ∗ unallocated {[client_1_addr]}
      ∗ unallocated {[client_2_addr]}
      ∗ unallocated {[client_3_addr]}
      ∗ free_ip (ip_of_address server_addr)
      ∗ free_ip (ip_of_address client_1_addr)
      ∗ free_ip (ip_of_address client_2_addr)
      ∗ free_ip (ip_of_address client_3_addr) }}}
      example_runner @["system"]
    {{{ v, RET v; True }}}.
  Proof.
     iMod (SI_init_module _ {[client_1_addr; client_2_addr; client_3_addr]})
      as (SI_res) "(mem & KVS_Init & #Hginv & Hcc & %specs)";
         first done.
    iMod (own_alloc (Excl ())) as "(%γx & Fx)"; first done.
    iMod (own_alloc (Excl ())) as "(%γy & Fy)"; first done.
    iMod (inv_alloc client_inv_name ⊤ (client_inv γx γy) with "[mem]") as "#Hinv".
    { rewrite big_sepS_insert//big_sepS_singleton.
      iDestruct "mem" as "[Hx Hy]". iFrame. }
    iIntros (Φ) "(Hsrvhist & Hcli1hist & Hcli2hist & Hcli3hist & Hsrvunalloc & Hcli1unalloc
    & Hcli2unalloc & Hcli3unalloc & ? & ? & ? & ?) HΦ".
    rewrite /example_runner.
    wp_pures.
    wp_apply (aneris_wp_socket_interp_alloc_singleton KVS_si with "Hsrvunalloc").
    iIntros "#HKVS_si".
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iDestruct (big_sepS_delete _  _ client_1_addr with "Hcc")
      as "(Hcc1 & Hcc)";
    first set_solver.
    iDestruct (big_sepS_delete _  _ client_2_addr with "Hcc")
      as "(Hcc2 & Hcc)";
    first set_solver.
    iDestruct (big_sepS_delete _  _ client_3_addr with "Hcc")
      as "(Hcc3 & _)";
    first set_solver.
    iSplitR "Hsrvhist KVS_Init".
    - iModIntro. wp_pures.
      wp_apply (aneris_wp_start {[80%positive : port]}).
      iFrame.
      iSplitR "Hcli1hist Hcli1unalloc Hcc1 Fx".
      + iModIntro. wp_pures.
        wp_apply (aneris_wp_start {[80%positive : port]}).
        iFrame.
        iSplitR "Hcli2hist Hcli2unalloc Hcc2 Fy".
        * iModIntro. wp_pures.
        wp_apply (aneris_wp_start {[80%positive : port]}).
        iFrame. iSplitL "HΦ".
          -- by iApply "HΦ".
          -- iIntros "!> Hports".  wp_apply (client_3_spec with "[$]"); try done.
        * iIntros "!> Hports". wp_apply (client_2_spec with "[$]"); try done.
      + iIntros "!> Hports". wp_apply (client_1_spec with "[$]"); try done.
    - iIntros "!> Hports". wp_apply (server_spec with "[$]"); try done.
      Unshelve. all: by destruct specs as (?&?&?&?&?&?); eauto.
  Qed.

End proof_runner.

Definition unit_model := model _ (λ _ _, False) ().
Lemma unit_model_rel_finitary : aneris_model_rel_finitary unit_model.
Proof. intros ?. apply finite_smaller_card_nat. apply _. Qed.

Definition ips : gset string :=
  {[ ip_of_address server_addr ; ip_of_address client_1_addr
  ; ip_of_address client_2_addr ; ip_of_address client_3_addr ]}.

Definition sa_dom : gset socket_address :=
  {[ server_addr ; client_1_addr; client_2_addr; client_3_addr ]}.

Definition init_state :=
  {|
    state_heaps := {["system" := ∅ ]};
    state_sockets := {["system" := ∅ ]};
    state_ms := ∅;
    state_trace := [];
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
  do 3 (iDestruct (unallocated_split with "Hunallocated") as "[Hunallocated ?]";
  [set_solver|]). iFrame.
  do 3 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
  iDestruct "Hhist" as "[Hhist ?]"; iFrame).
  do 3 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
  iDestruct "Hips" as "[Hips ?]"; iFrame).
Qed.  *)
