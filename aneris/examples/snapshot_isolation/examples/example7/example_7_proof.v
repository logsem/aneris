From aneris.aneris_lang Require Import network resources proofmode.
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
From aneris.examples.snapshot_isolation.examples.example7 Require Import example_7_code.
Import ser_inj.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.
From aneris.examples.snapshot_isolation.util Require Import util_proof.

Definition server_addr := SocketAddressInet "0.0.0.0" 80.
Definition client_1_addr := SocketAddressInet "0.0.0.1" 80.
Definition client_2_addr := SocketAddressInet "0.0.0.2" 80.
Definition client_3_addr := SocketAddressInet "0.0.0.3" 80.

Program Instance params : User_params :=
{| KVS_address := server_addr;
  KVS_keys := {["x"; "y"]};
  KVS_InvName := nroot .@ "siinv";
  KVS_serialization := int_serialization;
  KVS_ser_inj := int_ser_is_ser_injective;
  KVS_ser_inj_alt := int_ser_is_ser_injective_alt
|}.

Definition client_inv_name := nroot.@"clinv".

Section proofs.

Context `{!anerisG Mdl Σ, !SI_resources Mdl Σ, !SI_specs}.

  Definition client_inv : iProp Σ :=
  ∃ h, "x" ↦ₖ h ∗ "y" ↦ₖ h.

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

  Lemma transaction ip port client_addr (number : nat) :
  ip = ip_of_address client_addr →
  port = port_of_address client_addr →
  {{{ inv client_inv_name client_inv
    ∗ client_addr ⤳ (∅, ∅)
    ∗ unallocated {[client_addr]}
    ∗ free_ports ip {[port]}
    ∗ KVS_address ⤇ KVS_si }}}
    transaction $client_addr $KVS_address #number @[ip]
  {{{ v, RET v; True }}}.
  Proof.
    iIntros (Heqip Heqport Φ) "(#Hinv & Hmsghis & Hunalloc & Hports & Hprot) HΦ" .
    rewrite /transaction. wp_pures. rewrite Heqip Heqport.
    wp_apply (SI_init_client_proxy_spec with "[$Hunalloc $Hprot $Hmsghis $Hports]").
    iIntros (rpc) "Hcstate". wp_pures.
    wp_apply (SI_start_spec $! rpc client_addr (⊤ ∖ ↑client_inv_name)); try solve_ndisj.
    iInv (client_inv_name) as ">[%h[Hx Hy]]" "HClose".
    iModIntro. iFrame.
    iExists {["x" := h; "y" := h]}.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hy Hx".
    { iFrame. }
    iNext. iIntros "(Hcstate & [Hkx [Hky _]] & [Hcx [Hcy _]] & _)".
    iMod ("HClose" with "[Hkx Hky]") as "_".
    { iNext. iExists h. iFrame. }
    iModIntro. wp_pures.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #number) with "[] [Hcx]"). 
    set_solver. iFrame. iIntros "Hcx". wp_pures.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #number) with "[] [Hcy]").
    set_solver. iFrame. iIntros "Hcy". wp_pures.
    wp_apply (SI_commit_spec $! rpc client_addr (⊤ ∖ ↑client_inv_name));
    try solve_ndisj.
    iInv (client_inv_name) as ">[%h'[Hx Hy]]" "HClose".
    iModIntro.
    iExists {["x" := h'; "y" := h']}, _, 
    {["x" := (Some #number, true); "y" := (Some #number, true)]}.
    iFrame. iSplitL "Hcx Hcy Hx Hy".
      - iSplitR "Hcx Hcy Hx Hy"; try iSplitR "Hcx Hcy Hx Hy";
        try iPureIntro; try set_solver.
        rewrite !big_sepM_insert; try set_solver.
        rewrite !big_sepM_empty. iFrame.
      - iNext. iIntros (b) "[_ [[_ [_ HBig]] | [_ [_ HBig]]]]". 
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

  Lemma client_1_spec ip port :
    ip = ip_of_address client_1_addr →
    port = port_of_address client_1_addr →
    {{{ inv client_inv_name client_inv
      ∗ client_1_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_1_addr]}
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      client_1 $client_1_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (? ? Φ) "(#Hinv & ?) HΦ".
    rewrite /client_1. wp_pures.
    wp_apply (transaction ip port client_1_addr 1 with "[$]"); try done.
  Qed.

  Lemma client_2_spec ip port :
    ip = ip_of_address client_2_addr →
    port = port_of_address client_2_addr →
    {{{ inv client_inv_name client_inv
      ∗ client_2_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_2_addr]}
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      client_2 $client_2_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (? ? Φ) "(#Hinv & ?) HΦ".
    rewrite /client_2. wp_pures.
    wp_apply (transaction ip port client_2_addr 2 with "[$]"); try done.
  Qed.

  Lemma client_3_spec ip port client_3_addr :
    ip = ip_of_address client_3_addr →
    port = port_of_address client_3_addr →
    {{{ inv client_inv_name client_inv
      ∗ client_3_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_3_addr]}
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      client_3 $client_3_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Heqip Heqports Φ) "(#Hinv & Hmsghis & Hunalloc & Hports & Hprot) HΦ" .
    rewrite /client_3. wp_pures. rewrite Heqip Heqports.
    wp_apply (SI_init_client_proxy_spec with "[$Hunalloc $Hprot $Hmsghis $Hports]").
    iIntros (rpc) "Hcstate". wp_pures.
    wp_apply (SI_start_spec $! rpc client_3_addr (⊤ ∖ ↑client_inv_name));
    try solve_ndisj.
    iInv (client_inv_name) as ">[%h[Hx Hy]]" "HClose".
    iModIntro. iFrame.
    iExists {["x" := h; "y" := h]}.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hy Hx".
    { iFrame. }
    iNext. iIntros "(Hcstate & [Hkx [Hky _]] & [[Hcx Hsx] [[Hcy Hsy] _]] & _)".
    iMod ("HClose" with "[Hkx Hky]") as "_".
    { iNext. iExists h. iFrame. }
    iModIntro. wp_pures.
    wp_apply (SI_read_spec $! _ _ _ _ with "[] [Hcx]"); try set_solver.
    iFrame. iIntros "Hcx". wp_pures.
    wp_apply (SI_read_spec $! _ _ _ _ with "[] [Hcy]"); try set_solver.
    iFrame. iIntros "Hcy". wp_pures.
    wp_apply (SI_commit_spec $! rpc client_3_addr (⊤ ∖ ↑client_inv_name));
    try solve_ndisj.
    iInv (client_inv_name) as ">[%h'[Hx Hy]]" "HClose".
    iModIntro.
    iExists {["x" := h'; "y" := h']}, _, 
    {["x" := (hist_val h, false); "y" := (hist_val h, false)]}.
    iFrame. iSplitL "Hcx Hsx Hcy Hsy Hx Hy".
    - iSplitR "Hcx Hsx Hcy Hsy Hx Hy"; try iSplitR "Hcx Hsx Hcy Hsy Hx Hy";
      try iPureIntro; try set_solver.
      rewrite !big_sepM_insert; try set_solver.
      rewrite !big_sepM_empty. iFrame.
      - iNext. iIntros (b) "[_ [[_ [_ HBig]] | [_ [_ HBig]]]]". 
          + iMod ("HClose" with "[HBig]") as "_".
            * iNext. iExists _.
            rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "HBig" as "[[Hx _] [[Hy _] _]]". iFrame.
            * iModIntro. wp_pures. wp_lam. wp_pures. 
            destruct (hist_val h); wp_pures. 
              -- case_bool_decide as Heq; try set_solver.
                  wp_pures. by iApply "HΦ".
              -- by iApply "HΦ".
          + iMod ("HClose" with "[HBig]") as "_".
            * iNext. iExists h'.
            rewrite !big_sepM_insert; try set_solver. 
            iDestruct "HBig" as "[[? _] [[? _] _]]". by iFrame.
            * iModIntro. wp_pures. wp_lam. wp_pures.  
            destruct (hist_val h); wp_pures. 
              -- case_bool_decide as Heq; try set_solver.
                  wp_pures. by iApply "HΦ".
              -- by iApply "HΦ".
Qed.
  
End proofs.

Section proof_runner.

Context `{!anerisG Mdl Σ, !KVS_time, !SI_init}.

  Definition example_runner : expr :=
    let: "serveraddr" := MakeAddress #"0.0.0.0" #80 in
    let: "client1addr" := MakeAddress #"0.0.0.1" #80 in
    let: "client2addr" := MakeAddress #"0.0.0.2" #80 in
    let: "client3addr" := MakeAddress #"0.0.0.3" #80 in
    Start "0.0.0.0" (server "serveraddr") ;;
    Start "0.0.0.1" (client_1 "client1addr" "serveraddr") ;;
    Start "0.0.0.2" (client_2 "client2addr" "serveraddr") ;;
    Start "0.0.0.3" (client_3 "client3addr" "serveraddr").

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
    iMod (SI_init_module $! (I: True)) as (SI_res SI_specs) "(#GI' & HKVSres & HVKSinit)".
    iMod (inv_alloc client_inv_name ⊤ (client_inv) with "[HKVSres]") as "#Hinv".
    { iNext. iExists [].
    iDestruct (big_sepS_delete _ _ "x" with "HKVSres") as "(Hx & HKVSres)";
    first set_solver.
    iDestruct (big_sepS_delete _ _ "y" with "HKVSres") as "(Hy & _)";
    first set_solver. iFrame.
    }
    iIntros (Φ) "(Hsrvhist & Hcli1hist & Hcli2hist & Hcli3hist & Hsrvunalloc & Hcli1unalloc 
    & Hcli2unalloc & Hcli3unalloc & ? & ? & ? & ?) HΦ".
    rewrite /example_runner.
    wp_pures.
    wp_apply (aneris_wp_socket_interp_alloc_singleton KVS_si with "Hsrvunalloc").
    iIntros "#HKVS_si".
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "Hsrvhist HVKSinit".
    - iModIntro. wp_pures.
      wp_apply (aneris_wp_start {[80%positive : port]}).
      iFrame.
      iSplitR "Hcli1hist Hcli1unalloc".
      + iModIntro. wp_pures.
        wp_apply (aneris_wp_start {[80%positive : port]}).
        iFrame.
        iSplitR "Hcli2hist Hcli2unalloc".
        * iModIntro. wp_pures.
        wp_apply (aneris_wp_start {[80%positive : port]}).
        iFrame. iSplitL "HΦ". 
          -- by iApply "HΦ".
          -- iIntros "!> Hports".  wp_apply (client_3_spec with "[$]"); try done. 
        * iIntros "!> Hports". wp_apply (client_2_spec with "[$]"); try done. 
      + iIntros "!> Hports". wp_apply (client_1_spec with "[$]"); try done. 
    - iIntros "!> Hports". wp_apply (server_spec with "[$]"); done.
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

Global Instance SI_init_instance
`{!anerisG Mdl Σ} : SI_init.
Proof.
Admitted.

Theorem runner_safe :
  aneris_adequate example_runner "system" init_state (λ _, True).
Proof.
  set (Σ := #[anerisΣ unit_model]).
  apply (@adequacy Σ unit_model _ _ ips sa_dom ∅ ∅ ∅); try set_solver.
  { apply unit_model_rel_finitary. }
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