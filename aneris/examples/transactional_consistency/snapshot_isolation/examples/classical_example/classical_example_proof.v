From aneris.aneris_lang Require Import network resources proofmode.
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
From aneris.examples.transactional_consistency.snapshot_isolation.examples.classical_example
      Require Import classical_example_code.
Import ser_inj.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation Require Import
     snapshot_isolation_api_implementation
     instantiation_of_init.
From aneris.examples.transactional_consistency.snapshot_isolation.util Require Import util_proof.
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

Context `{!anerisG Mdl Σ, !SI_resources Mdl Σ}.

  Definition client_inv : iProp Σ :=
  ∃ h, "x" ↦ₖ h ∗ "y" ↦ₖ h.

  Lemma server_spec :
    SI_client_toolbox -∗
    {{{ KVS_Init
      ∗ KVS_address ⤳ (∅, ∅)
      ∗ free_ports (ip_of_address KVS_address) {[port_of_address KVS_address]}
      ∗ KVS_address ⤇ KVS_si }}}
    server #KVS_address @[ip_of_address KVS_address]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (KVS_Init & ∅ & free & #KVS_si) HΦ".
    rewrite /server. wp_pures. 
    by wp_apply ("Hinit_kvs" with "[$KVS_si $KVS_Init $∅ $free]").
  Qed.

  Lemma client_1_spec ip port :
    ip = ip_of_address client_1_addr →
    port = port_of_address client_1_addr →
    SI_client_toolbox -∗
    {{{ inv client_inv_name client_inv
      ∗ client_1_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_1_addr]}
      ∗ KVS_ClientCanConnect client_1_addr
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      transaction1_client $client_1_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (-> ->) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) 
      %Φ !> (#Hinv & Hmsghis & Hunalloc & Hcc & Hports & Hprot) HΦ" .
    rewrite /transaction1_client. wp_pures.
    wp_apply ("Hinit_cli" with "[$Hunalloc $Hprot $Hmsghis $Hports $Hcc]").
    iIntros (rpc) "(Hcstate & #HiC)".
    wp_pures. rewrite /transaction1. wp_pures.
    wp_apply ("Hst" $! _ _ (⊤ ∖ ↑client_inv_name)); try solve_ndisj.
    iInv (client_inv_name) as ">[%h[Hx Hy]]" "HClose".
    iModIntro. iFrame.
    iExists {["x" := h; "y" := h]}.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hy Hx".
    { iFrame. }
    iIntros "(Hcstate & [Hkx [Hky _]] & [Hcx [Hcy _]] & _)".
    iMod ("HClose" with "[Hkx Hky]") as "_".
    { iNext. iExists h. iFrame. }
    iModIntro. wp_pures.
    wp_apply ("Hwr"  $! _ _ ⊤ _ (SerVal #1) with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _, _.
    iFrame.
    iIntros "Hcx".
    iModIntro.
    wp_pures.
    wp_apply ("Hwr"  $! _ _ ⊤ _ (SerVal #1) with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _, _.
    iFrame.
    iIntros "Hcy".
    iModIntro.
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; try eauto.
    iFrame "#".
    iInv (client_inv_name) as ">[%h'[Hx Hy]]" "HClose".
    iModIntro.
    iExists {["x" := h'; "y" := h']}, _,
    {["x" := (Some #1, true); "y" := (Some #1, true)]}.
    iFrame. iSplitL "Hcx Hcy Hx Hy".
      - iSplitR "Hcx Hcy Hx Hy"; try iSplitR "Hcx Hcy Hx Hy";
        try iPureIntro; try set_solver.
        rewrite !big_sepM_insert; try set_solver.
        rewrite !big_sepM_empty. iFrame.
      - iIntros "[_ [[_ HBig] | [_ HBig]]]".
          + iMod ("HClose" with "[HBig]") as "_".
            * iNext. iExists _.
              rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "HBig" as "[[Hx _] [[Hy _] _]]". by iFrame.
            * iModIntro. by iApply "HΦ".
          + iMod ("HClose" with "[HBig]") as "_".
            * iNext. iExists h'.
              rewrite !big_sepM_insert; try set_solver.
              iDestruct "HBig" as "[[? _] [[? _] _]]". by iFrame.
            * iModIntro. by iApply "HΦ".
  Qed.

  Lemma client_2_spec ip port :
    ip = ip_of_address client_2_addr →
    port = port_of_address client_2_addr →
    SI_client_toolbox -∗
    {{{ inv client_inv_name client_inv
      ∗ client_2_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_2_addr]}
      ∗ KVS_ClientCanConnect client_2_addr
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      transaction2_client $client_2_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (-> ->) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) 
      %Φ !> (#Hinv & Hmsghis & Hunalloc & Hcc & Hports & Hprot) HΦ" .
    rewrite /transaction2_client. wp_pures.
    wp_apply ("Hinit_cli" with "[$Hunalloc $Hprot $Hmsghis $Hports $Hcc]").
    iIntros (rpc) "(Hcstate & #HiC)".
    wp_pures. rewrite /transaction2. wp_pures.
    wp_apply ("Hst" $! _ _ (⊤ ∖ ↑client_inv_name)); try solve_ndisj.
    iInv (client_inv_name) as ">[%h[Hx Hy]]" "HClose".
    iModIntro. iFrame.
    iExists {["x" := h; "y" := h]}.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hy Hx".
    { iFrame. }
    iIntros "(Hcstate & [Hkx [Hky _]] & [Hcx [Hcy _]] & _)".
    iMod ("HClose" with "[Hkx Hky]") as "_".
    { iNext. iExists h. iFrame. }
    iModIntro. wp_pures.
    wp_apply ("Hwr"  $! _ _ ⊤ _ (SerVal #2) with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _, _.
    iFrame.
    iIntros "Hcx".
    iModIntro.
    wp_pures.
    wp_apply ("Hwr"  $! _ _ ⊤ _ (SerVal #2) with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _, _.
    iFrame.
    iIntros "Hcy".
    iModIntro.
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; try eauto.
    iFrame "#".
    iInv (client_inv_name) as ">[%h'[Hx Hy]]" "HClose".
    iModIntro.
    iExists {["x" := h'; "y" := h']}, _,
    {["x" := (Some #2, true); "y" := (Some #2, true)]}.
    iFrame. iSplitL "Hcx Hcy Hx Hy".
      - iSplitR "Hcx Hcy Hx Hy"; try iSplitR "Hcx Hcy Hx Hy";
        try iPureIntro; try set_solver.
        rewrite !big_sepM_insert; try set_solver.
        rewrite !big_sepM_empty. iFrame.
      - iIntros "[_ [[_ HBig] | [_ HBig]]]".
          + iMod ("HClose" with "[HBig]") as "_".
            * iNext. iExists _.
              rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "HBig" as "[[Hx _] [[Hy _] _]]". by iFrame.
            * iModIntro. by iApply "HΦ".
          + iMod ("HClose" with "[HBig]") as "_".
            * iNext. iExists h'.
              rewrite !big_sepM_insert; try set_solver.
              iDestruct "HBig" as "[[? _] [[? _] _]]". by iFrame.
            * iModIntro. by iApply "HΦ".
  Qed.

  Lemma client_3_spec ip port client_3_addr :
    ip = ip_of_address client_3_addr →
    port = port_of_address client_3_addr →
    SI_client_toolbox -∗
    {{{ inv client_inv_name client_inv
      ∗ client_3_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_3_addr]}
      ∗ KVS_ClientCanConnect client_3_addr
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      transaction3_client $client_3_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (-> ->) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) 
      %Φ !>(#Hinv & Hmsghis & Hunalloc & Hports & Hcc & Hprot) HΦ".
    rewrite /transaction3_client. wp_pures.
    wp_apply ("Hinit_cli" with "[$Hunalloc $Hprot $Hmsghis $Hports $Hcc]").
    iIntros (rpc) "(Hcstate & #HiC)". wp_pures. rewrite /transaction3. wp_pures.
    wp_apply ("Hst" $! _ _ (⊤ ∖ ↑client_inv_name)); try solve_ndisj.
    iInv (client_inv_name) as ">[%h[Hx Hy]]" "HClose".
    iModIntro. iFrame.
    iExists {["x" := h; "y" := h]}.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hy Hx".
    { iFrame. }
    iIntros "(Hcstate & [Hkx [Hky _]] & [[Hcx Hsx] [[Hcy Hsy] _]] & _)".
    iMod ("HClose" with "[Hkx Hky]") as "_".
    { iNext. iExists h. iFrame. }
    iModIntro. wp_pures.
    wp_apply ("Hrd" $! _ _ ⊤ with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _.
    iFrame.
    iIntros "Hcx".
    iModIntro.
    wp_pures.
    wp_apply ("Hrd" $! _ _ ⊤ with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _.
    iFrame.
    iIntros "Hcy".
    iModIntro.
    wp_pures.
    destruct (last h); wp_pures; do 2 wp_lam; wp_pures.
      - case_bool_decide as Heq; try set_solver. wp_pures.
        wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; try eauto.
        iFrame "#".
        iInv (client_inv_name) as ">[%h'[Hx Hy]]" "HClose".
        iModIntro.
        iExists {["x" := h'; "y" := h']}, _,
        {["x" := (Some v, false); "y" := (Some v, false)]}.
        iFrame. iSplitL "Hcx Hsx Hcy Hsy Hx Hy".
        + iSplitR "Hcx Hsx Hcy Hsy Hx Hy"; try iSplitR "Hcx Hsx Hcy Hsy Hx Hy";
          try iPureIntro; try set_solver.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
        + iIntros "[_ [[_ HBig] | [_ HBig]]]".
            * iMod ("HClose" with "[HBig]") as "_".
              -- iNext. iExists _.
                rewrite !(big_sepM2_insert); try set_solver.
                iDestruct "HBig" as "[[Hx _] [[Hy _] _]]". iFrame.
              -- iModIntro. by iApply "HΦ".
            * iMod ("HClose" with "[HBig]") as "_".
              -- iNext. iExists h'.
                rewrite !big_sepM_insert; try set_solver.
                iDestruct "HBig" as "[[? _] [[? _] _]]". by iFrame.
              -- iModIntro. by iApply "HΦ".
      - wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; try eauto.
        iFrame "#".
        iInv (client_inv_name) as ">[%h'[Hx Hy]]" "HClose".
        iModIntro.
        iExists {["x" := h'; "y" := h']}, _,
        {["x" := (None, false); "y" := (None, false)]}.
        iFrame. iSplitL "Hcx Hsx Hcy Hsy Hx Hy".
        + iSplitR "Hcx Hsx Hcy Hsy Hx Hy"; try iSplitR "Hcx Hsx Hcy Hsy Hx Hy";
          try iPureIntro; try set_solver.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
        + iIntros "[_ [[_ HBig] | [_ HBig]]]".
          * iMod ("HClose" with "[HBig]") as "_".
            -- iNext. iExists _.
              rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "HBig" as "[[Hx _] [[Hy _] _]]". iFrame.
            -- iModIntro. by iApply "HΦ".
          * iMod ("HClose" with "[HBig]") as "_".
            -- iNext. iExists h'.
              rewrite !big_sepM_insert; try set_solver.
              iDestruct "HBig" as "[[? _] [[? _] _]]". by iFrame.
            -- iModIntro. by iApply "HΦ".
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
    iIntros (Φ) "(srv_∅ & clt1_∅ & clt2_∅ & clt3_∅ & srv_unalloc & clt1_unalloc &
            clt2_unalloc & clt3_unalloc & srv_free & clt1_free & clt2_free & clt3_free)
              HΦ".
    iMod (SI_init_module _ {[client_1_addr; client_2_addr; client_3_addr]})
      as (SI_res) "(mem & KVS_Init & #Hginv & Hcc & #specs)";
         first done.
    iMod (inv_alloc client_inv_name ⊤ (client_inv) with "[mem]") as "#Hinv".
    { 
      iNext. iExists [].
      iDestruct (big_sepS_delete _ _ "x" with "mem") as "(Hx & HKVSres)";
      first set_solver.
      iDestruct (big_sepS_delete _ _ "y" with "HKVSres") as "(Hy & _)";
      first set_solver. iFrame.
    }
    rewrite /example_runner.
    wp_pures.
    wp_apply (aneris_wp_socket_interp_alloc_singleton KVS_si with "srv_unalloc").
    iIntros "#KVS_si".
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "KVS_Init srv_∅"; last first.
    { iIntros "!>free". by wp_apply (server_spec with "[$] [$]"). }
    iNext.
    wp_pures.
    iDestruct (big_sepS_delete _  _ client_1_addr with "Hcc")
      as "(Hcc1 & Hcc)";
    first set_solver.
    iDestruct (big_sepS_delete _  _ client_2_addr with "Hcc")
      as "(Hcc2 & Hcc)";
    first set_solver.
    iDestruct (big_sepS_delete _  _ client_3_addr with "Hcc")
      as "(Hcc3 & _)";
    first set_solver.
    wp_apply (aneris_wp_start {[80%positive]}).
    iSplitL "clt1_free"; first done.
    iSplitR "clt1_∅ clt1_unalloc Hcc1"; last first.
    {
      iIntros "!>free".
      wp_apply (client_1_spec with "[$][$]"); try done.
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iSplitL "clt2_free"; first done.
    iSplitR "clt2_∅ clt2_unalloc Hcc2"; last first.
    {
      iIntros "!>free".
      wp_apply (client_2_spec with "[$][$]"); try done.
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iSplitL "clt3_free"; first done.
    iSplitR "clt3_∅ clt3_unalloc Hcc3"; last first.
    {
      iIntros "!>free".
      wp_apply (client_3_spec with "[$][$]"); try done.
    }
    iNext.
    by iApply "HΦ".
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
Qed. 
