From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params resources specs derived_specs.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.snapshot_isolation.specs Require Import
  user_params time events aux_defs resource_algebras resources specs.
From aneris.examples.snapshot_isolation.examples.classical_example_run
      Require Import classical_example_run_code.
Import ser_inj.
From aneris.examples.snapshot_isolation.instantiation Require Import
     snapshot_isolation_api_implementation
     instantiation_of_init.
From aneris.examples.snapshot_isolation.util Require Import util_proof.

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

Context `{!anerisG Mdl Σ, !SI_resources Mdl Σ, !SI_client_toolbox}.

  Definition client_inv : iProp Σ :=
  ∃ vo, OwnMemKeyVal "x" vo ∗ OwnMemKeyVal "y" vo.

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

  Lemma client_1_spec ip port :
    ip = ip_of_address client_1_addr →
    port = port_of_address client_1_addr →
    {{{ inv client_inv_name client_inv
      ∗ client_1_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_1_addr]}
      ∗ KVS_ClientCanConnect client_1_addr
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      transaction1_client $client_1_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Heqip Heqport Φ) "(#Hinv & Hmsghis & Hunalloc & Hcc & Hports & Hprot) HΦ" .
    rewrite /transaction1_client. wp_pures. rewrite Heqip Heqport.
    wp_apply (init_client_proxy_spec_derived
               with "[] [$Hunalloc $Hprot $Hmsghis $Hports $Hcc]").
    { iPureIntro. apply SI_init_client_proxy_spec. }
    iIntros (rpc) "(Hcstate & #HiC)".
    wp_pures.
    wp_apply (run_spec_derived_generic rpc _ client_1_addr (⊤ ∖ ↑client_inv_name)
      (λ msnap, ⌜∃ vo, msnap = {["x" := vo; "y" := vo]}⌝)%I 
      (λ msnap mc, ⌜mc = {["x" := (Some #1, true); "y" := (Some #1, true)]}⌝)%I
      with "[][][][][][][][$Hcstate][HΦ]"); try solve_ndisj.
    - iPureIntro. apply SI_start_spec. 
    - iPureIntro. apply SI_commit_spec.
    - iPureIntro. apply _.
    - iModIntro.
      iInv (client_inv_name) as ">[%vo [Hx Hy]]" "HClose".
      iModIntro. iExists {["x" := vo; "y" := vo]}.
      iSplit. { iPureIntro. by exists vo. }
      rewrite !big_sepM_insert; try set_solver.
      rewrite big_sepM_empty. iFrame.
      iNext. iIntros "(Hx & Hy & _)".
      iMod ("HClose" with "[Hx Hy]") as "_".
      { iNext. iExists vo. iFrame. }
      iModIntro. iIntros (mc).
      iInv (client_inv_name) as ">[%vo'[Hx Hy]]" "HClose".
      iModIntro. iExists {["x" := vo'; "y" := vo']}.
      rewrite !big_sepM_insert; try set_solver.
      rewrite big_sepM_empty. iFrame.
      iSplit. { iPureIntro. set_solver. }
      iIntros ">[(-> & Hkeys) | (Hx & Hy & _)]".
      + iMod ("HClose" with "[Hkeys]") as "_"; last done.
        iNext. iExists (Some (#1)).
        rewrite !big_sepM2_insert; try set_solver.
        iDestruct "Hkeys" as "(Hx & Hy & _)". iFrame.
      + iMod ("HClose" with "[Hx Hy]") as "_"; last done.
        iNext. iExists vo'. iFrame.
    - iIntros (msnap Φ') "!# (H_cache & [%h ->]) HΦ'".
      rewrite /transaction1. wp_pures.
      rewrite !big_sepM_insert; try set_solver.
      iDestruct "H_cache" as "(H_cx & H_cy & _)".
      wp_apply (SI_write_spec  _ _ _ _ (SerVal #1) with "[][$][H_cx]").
      set_solver. iFrame "#∗". iIntros "Hcx". wp_pures.
      wp_apply (SI_write_spec  _ _ _ _ (SerVal #1) with "[][$][H_cy]").
      set_solver. iFrame "#∗". iIntros "Hcy".
      iApply ("HΦ'" $! {["x" := (Some #1, true); "y" := (Some #1, true)]}).
      iSplit. { iPureIntro. set_solver. }
      iSplit; last done.
      rewrite !big_sepM_insert; try set_solver.
      rewrite big_sepM_empty. iFrame.
    - iNext. iIntros. by iApply "HΦ".
  Qed.

  Lemma client_2_spec ip port :
    ip = ip_of_address client_2_addr →
    port = port_of_address client_2_addr →
    {{{ inv client_inv_name client_inv
      ∗ client_2_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_2_addr]}
      ∗ KVS_ClientCanConnect client_2_addr
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      transaction2_client $client_2_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Heqip Heqport Φ) "(#Hinv & Hmsghis & Hunalloc & Hcc & Hports & Hprot) HΦ" .
    rewrite /transaction2_client. wp_pures. rewrite Heqip Heqport.
    wp_apply (init_client_proxy_spec_derived
               with "[] [$Hunalloc $Hprot $Hmsghis $Hports $Hcc]").
    { iPureIntro. apply SI_init_client_proxy_spec. }
    iIntros (rpc) "(Hcstate & #HiC)".
    wp_pures.
    wp_apply (run_spec_derived_generic rpc _ client_2_addr (⊤ ∖ ↑client_inv_name)
      (λ msnap, ⌜∃ vo, msnap = {["x" := vo; "y" := vo]}⌝)%I 
      (λ msnap mc, ⌜mc = {["x" := (Some #2, true); "y" := (Some #2, true)]}⌝)%I
      with "[][][][][][][][$Hcstate][HΦ]"); try solve_ndisj.
    - iPureIntro. apply SI_start_spec. 
    - iPureIntro. apply SI_commit_spec.
    - iPureIntro. apply _.
    - iModIntro.
      iInv (client_inv_name) as ">[%vo [Hx Hy]]" "HClose".
      iModIntro. iExists {["x" := vo; "y" := vo]}.
      iSplit. { iPureIntro. by exists vo. }
      rewrite !big_sepM_insert; try set_solver.
      rewrite big_sepM_empty. iFrame.
      iNext. iIntros "(Hx & Hy & _)".
      iMod ("HClose" with "[Hx Hy]") as "_".
      { iNext. iExists vo. iFrame. }
      iModIntro. iIntros (mc).
      iInv (client_inv_name) as ">[%vo'[Hx Hy]]" "HClose".
      iModIntro. iExists {["x" := vo'; "y" := vo']}.
      rewrite !big_sepM_insert; try set_solver.
      rewrite big_sepM_empty. iFrame.
      iSplit. { iPureIntro. set_solver. }
      iIntros ">[(-> & Hkeys) | (Hx & Hy & _)]".
      + iMod ("HClose" with "[Hkeys]") as "_"; last done.
        iNext. iExists (Some (#2)).
        rewrite !big_sepM2_insert; try set_solver.
        iDestruct "Hkeys" as "(Hx & Hy & _)". iFrame.
      + iMod ("HClose" with "[Hx Hy]") as "_"; last done.
        iNext. iExists vo'. iFrame.
    - iIntros (msnap Φ') "!# (H_cache & [%h ->]) HΦ'".
      rewrite /transaction2. wp_pures.
      rewrite !big_sepM_insert; try set_solver.
      iDestruct "H_cache" as "(H_cx & H_cy & _)".
      wp_apply (SI_write_spec  _ _ _ _ (SerVal #2) with "[][$][H_cx]").
      set_solver. iFrame "#∗". iIntros "Hcx". wp_pures.
      wp_apply (SI_write_spec  _ _ _ _ (SerVal #2) with "[][$][H_cy]").
      set_solver. iFrame "#∗". iIntros "Hcy".
      iApply ("HΦ'" $! {["x" := (Some #2, true); "y" := (Some #2, true)]}).
      iSplit. { iPureIntro. set_solver. }
      iSplit; last done.
      rewrite !big_sepM_insert; try set_solver.
      rewrite big_sepM_empty. iFrame.
    - iNext. iIntros. by iApply "HΦ".
  Qed.

  Lemma client_3_spec ip port client_3_addr :
    ip = ip_of_address client_3_addr →
    port = port_of_address client_3_addr →
    {{{ inv client_inv_name client_inv
      ∗ client_3_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_3_addr]}
      ∗ KVS_ClientCanConnect client_3_addr
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      transaction3_client $client_3_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Heqip Heqport Φ) "(#Hinv & Hmsghis & Hunalloc & Hcc & Hports & Hprot) HΦ" .
    rewrite /transaction3_client. wp_pures. rewrite Heqip Heqport.
    wp_apply (init_client_proxy_spec_derived
               with "[] [$Hunalloc $Hprot $Hmsghis $Hports $Hcc]").
    { iPureIntro. apply SI_init_client_proxy_spec. }
    iIntros (rpc) "(Hcstate & #HiC)".
    wp_pures.
    wp_apply (run_spec_derived_generic rpc _ client_3_addr (⊤ ∖ ↑client_inv_name)
      (λ msnap, ⌜∃ vo, msnap = {["x" := vo; "y" := vo]}⌝)%I 
      (λ msnap mc, ⌜∃ vo1 vo2, mc = {["x" := (vo1, false); "y" := (vo2, false)]}⌝)%I
      with "[][][][][][][][$Hcstate][HΦ]"); try solve_ndisj.
    - iPureIntro. apply SI_start_spec. 
    - iPureIntro. apply SI_commit_spec.
    - iPureIntro. apply _.
    - iModIntro.
      iInv (client_inv_name) as ">[%vo [Hx Hy]]" "HClose".
      iModIntro. iExists {["x" := vo; "y" := vo]}.
      iSplit. { iPureIntro. by exists vo. }
      rewrite !big_sepM_insert; try set_solver.
      rewrite big_sepM_empty. iFrame.
      iNext. iIntros "(Hx & Hy & _)".
      iMod ("HClose" with "[Hx Hy]") as "_".
      { iNext. iExists vo. iFrame. }
      iModIntro. iIntros (mc).
      iInv (client_inv_name) as ">[%vo'[Hx Hy]]" "HClose".
      iModIntro. iExists {["x" := vo'; "y" := vo']}.
      rewrite !big_sepM_insert; try set_solver.
      rewrite big_sepM_empty. iFrame.
      iSplit. { iPureIntro. set_solver. }
      iIntros ">[ ([%vo1 [%vo2 ->]] & Hkeys) | (Hx & Hy & _)]".
      + iMod ("HClose" with "[Hkeys]") as "_"; last done.
        iNext. iExists vo'.
        rewrite !big_sepM2_insert; try set_solver.
        iDestruct "Hkeys" as "(Hx & Hy & _)".
        destruct vo1, vo2; iFrame.
      + iMod ("HClose" with "[Hx Hy]") as "_"; last done.
        iNext. iExists vo'. iFrame.
    - iIntros (msnap Φ') "!# (H_cache & [%vo ->]) HΦ'".
      rewrite /transaction3. wp_pures.
      rewrite !big_sepM_insert; try set_solver.
      iDestruct "H_cache" as "((H_cx & H_cx_s) & (H_cy & H_cy_s) & _)".
      wp_apply (SI_read_spec _ _ _ _ with "[][$][H_cx]"); try set_solver.
      iFrame "#∗". iIntros "H_cx". wp_pures.
      wp_apply (SI_read_spec _ _ _ _ with "[][$][H_cy]"); try set_solver.
      iFrame "#∗". iIntros "H_cy". wp_pures.
      destruct vo; do 2 wp_lam; wp_pures. 
      + case_bool_decide as Heq; try set_solver. wp_pures.
        iApply ("HΦ'" $! {["x" := (Some v, false); "y" := (Some v, false)]}).
        iSplit. { iPureIntro. set_solver. }
        iSplit; last set_solver.
        rewrite !big_sepM_insert; try set_solver.
        rewrite big_sepM_empty. iFrame.
      + iApply ("HΦ'" $! {["x" := (None, false); "y" := (None, false)]}).
        iSplit. { iPureIntro. set_solver. }
        iSplit; last set_solver.
        rewrite !big_sepM_insert; try set_solver.
        rewrite big_sepM_empty. iFrame.
    - iNext. iIntros. by iApply "HΦ".
  Qed.

End proofs.

Section proof_runner.

Context `{!anerisG Mdl Σ, !SI_init}.

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
    iMod (inv_alloc client_inv_name ⊤ (client_inv) with "[mem]") as "#Hinv".
    { iNext. iExists None.
    iDestruct (big_sepS_delete _ _ "x" with "mem") as "(Hx & HKVSres)";
    first set_solver.
    iDestruct (big_sepS_delete _ _ "y" with "HKVSres") as "(Hy & _)";
    first set_solver.
    iSplitR "Hy".
    all : iExists [].
    all : by iFrame.
    }
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
      iSplitR "Hcli1hist Hcli1unalloc Hcc1".
      + iModIntro. wp_pures.
        wp_apply (aneris_wp_start {[80%positive : port]}).
        iFrame.
        iSplitR "Hcli2hist Hcli2unalloc Hcc2".
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
Qed.