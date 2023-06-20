(* From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params.
From aneris.examples.snapshot_isolation.specs.specs_deprecated
     Require Import resources_points_to_with_key_status specs_points_to_with_key_status.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.snapshot_isolation.examples.example8 Require Import example_8_code.
From iris.algebra Require Import excl.
Import ser_inj.
From aneris.examples.snapshot_isolation.util.util_deprecated Require Import util_proof.

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

Section proofs.

Context `{!anerisG Mdl Σ, !KVS_time, !KVSG Σ,
!SI_resources Mdl Σ}.

  Definition token (γ : gname) : iProp Σ := own γ (Excl ()).

  Lemma token_exclusive (γ : gname) : token γ -∗ token γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Definition client_inv (γS1 γS2 γF1 γF2 : gname): iProp Σ :=
    ("x" ↦ₖ None ∗ token γS1 ∗ token γS2) ∨ 
    (∃ wx, "x" ↦ₖ Some wx ∗ ⌜we_val wx = #1⌝ ∗ token γF1 ∗ token γS2) ∨ 
    (∃ wx, "x" ↦ₖ Some wx ∗ ⌜we_val wx = #1⌝ ∗ token γF1 ∗ token γF2).

  Definition client_specs : iProp Σ :=
    init_client_proxy_spec ∗ start_spec ∗ read_spec ∗ write_spec ∗ commit_spec.

  Lemma server_spec ip port :
    ip = ip_of_address KVS_address →
    port = port_of_address KVS_address →
    {{{ KVS_Init
      ∗ init_kvs_spec
      ∗ KVS_address ⤳ (∅, ∅)
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
    server #KVS_address @[ip]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (H3 H4 Φ) "(HKVSInit & HKVSInitspec & H5 & H6 & H7) HΦ".
    rewrite /server. wp_pures. rewrite H3 H4.
    by wp_apply ("HKVSInitspec" with "[$]").
  Qed.

  Lemma client_1_spec ip port (γS1 γS2 γF1 γF2 : gname) :
    ip = ip_of_address client_1_addr →
    port = port_of_address client_1_addr →
    {{{ client_specs
      ∗ token γF1
      ∗ inv client_inv_name (client_inv γS1 γS2 γF1 γF2)
      ∗ client_1_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_1_addr]}
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      client_1 $client_1_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (H1 H2 Φ) "((#HInit & #HStart & #HRead & #HWrite & #HCommit) & Hftk1 & #Hinv & H3 & H4 & H5 & H6) HΦ" .
    rewrite /client_1. wp_pures. rewrite H1 H2.
    wp_apply ("HInit" with "[$]").
    iIntros (rpc) "Hcstate". wp_pures.
    wp_apply ("HStart" $! rpc client_1_addr (⊤ ∖ ↑client_inv_name)); try solve_ndisj.
    iInv (client_inv_name) as ">HOpen" "HClose".
    iModIntro. iFrame. unfold client_inv.
    iDestruct "HOpen" as "[[Hx [Hstk1 Hstk2]] | [Hcase | Hcase]]";
    try (iDestruct "Hcase" as (?) "[_ [_ [Hftk1' _]]]";
    iDestruct (token_exclusive with "Hftk1 Hftk1'") as "[]").
    iExists {["x" := None]}.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty. iSplitL "Hx". iFrame.
    iNext. iIntros "(H3 & [H4  _] & [H5 H5'] & _)".
    iMod ("HClose" with "[H4 Hstk1 Hstk2]") as "_".
    {iLeft. iNext. iFrame. }
    iModIntro. wp_pures.
    wp_apply ("HWrite" $! _ _ _ _ (SerVal #1) with "[] [$H5 $H5']").
    set_solver. iIntros "(H5 & H5')". wp_pures. 
    wp_apply (commitT_spec _ _ (⊤ ∖ ↑client_inv_name) with "[] [] [Hftk1 HΦ H3 H5 H5']");
    try solve_ndisj.
    iInv (client_inv_name) as ">HOpen" "HClose".
    iModIntro. iDestruct "HOpen" as "[[Hx [Hstk1 Hstk2]] | [Hcase | Hcase]]";
    try (iDestruct "Hcase" as (?) "[_ [_ [Hftk1' _]]]";
    iDestruct (token_exclusive with "Hftk1 Hftk1'") as "[]").
    iExists {["x" := None]}, {["x" := None]}, {["x" := (Some #1, true)]}. 
    iSplitR "Hstk1 Hstk2 Hftk1 HClose HΦ".
      - iFrame. iSplitR. {iPureIntro. unfold can_commit. set_solver. } 
      iSplitR. iPureIntro. set_solver.
      iSplitR. iPureIntro. set_solver.
      rewrite !big_sepM_insert; try set_solver.
      rewrite !big_sepM_empty. iFrame.
      - iModIntro. iIntros "[HBig1 HBig2]".
      iDestruct "HBig2" as (t) "[HBig2 HBig2']".
      rewrite !big_sepM2_insert; try set_solver.
      rewrite big_sepM2_empty. iDestruct "HBig2'" as "[Hx _]".
      iMod ("HClose" with "[Hx Hftk1 Hstk2]") as "_".
        + iNext. iRight. iLeft. simpl commit_event. iExists _. iFrame.
        by iPureIntro. 
        + iModIntro. by iApply "HΦ".
   Qed.

  Lemma client_2_spec ip port (γS1 γS2 γF1 γF2 : gname) :
    ip = ip_of_address client_2_addr →
    port = port_of_address client_2_addr →
    {{{ client_specs 
      ∗ token γF2
      ∗ inv client_inv_name (client_inv γS1 γS2 γF1 γF2)
      ∗ client_2_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_2_addr]}
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      client_2 $client_2_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (H1 H2 Φ) "((#HInit & #HStart & #HRead & #HWrite & #HCommit) & Hftk2 & #Hinv & H3 & H4 & H5 & H6) HΦ" .
    rewrite /client_2. wp_pures. rewrite H1 H2.
    wp_apply ("HInit" with "[$]").
    iIntros (rpc) "Hcstate". wp_pures.
    wp_apply ("HStart" $! rpc client_2_addr (⊤ ∖ ↑client_inv_name)); try solve_ndisj.
    iInv (client_inv_name) as ">HOpen" "HClose".
    iModIntro. iFrame. unfold client_inv.
    iDestruct "HOpen" as "[[Hx [Hstk1 Hstk2]] | [Hcase | Hcase]]".
    - iExists {["x" := None]}.
      rewrite !big_sepM_insert; try set_solver.
      rewrite big_sepM_empty. iFrame.
      iNext. iIntros "(H3 & [H4  _] & [H5 H5'] & _)".
      iMod ("HClose" with "[H4 Hstk1 Hstk2]") as "_".
      {iLeft. iNext. iFrame. }
      iModIntro. wp_pures.
      admit. 
    - iDestruct "Hcase" as (wx) "[Hx [#Heq [Hftk1 Hstk2]]]".
      iExists {["x" := Some wx]}.
      rewrite !big_sepM_insert; try set_solver.
      rewrite big_sepM_empty. iFrame.
      iNext. iIntros "(H3 & [H4  _] & [H5 H5'] & _)".
      iMod ("HClose" with "[H4 Hftk1 Hstk2]") as "_".
      {iNext. iRight. iLeft. iExists wx. by iFrame. }
      iModIntro. wp_pures. admit.
    - iDestruct "Hcase" as (?) "[_ [_ [_ Hftk2']]]";
      iDestruct (token_exclusive with "Hftk2 Hftk2'") as "[]".
  Admitted.

End proofs. 

Section proof_runner.
  
Context `{!anerisG Mdl Σ, !KVS_time, !SI_init, !KVSG Σ}.

  Definition example_runner : expr :=
    let: "serveraddr" := MakeAddress #"0.0.0.0" #80 in
    let: "client1addr" := MakeAddress #"0.0.0.1" #80 in
    let: "client2addr" := MakeAddress #"0.0.0.2" #80 in
    Start "0.0.0.0" (server "serveraddr") ;;
    Start "0.0.0.1" (client_1 "client1addr" "serveraddr") ;;
    Start "0.0.0.2" (client_2 "client2addr" "serveraddr").

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
    iMod (SI_init_module $! (I: True)) as (SIres) "(#H1' & H2' & #H3' & HKVSres & #H4' & [#H9' [#H10' [#H11' [#H12' H13]]]])".
    iMod (own_alloc (Excl ())) as (γS1) "Hstk1"; first done.
    iMod (own_alloc (Excl ())) as (γS2) "Hstk2"; first done.
    iMod (own_alloc (Excl ())) as (γF1) "Hftk1"; first done.
    iMod (own_alloc (Excl ())) as (γF2) "Hftk2"; first done.
    iMod (inv_alloc client_inv_name ⊤ (client_inv γS1 γS2 γF1 γF2) with "[H2' Hstk1 Hstk2]") as "#Hinv".
    { iModIntro. iLeft.
    iDestruct (big_sepS_delete _ _ "x" with "H2'") as "(Hx & H2')";
    first set_solver. iFrame. }
    iIntros (Φ) "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HΦ".
    rewrite /example_runner. wp_pures.
    wp_apply (aneris_wp_socket_interp_alloc_singleton KVS_si with "H4").
    iIntros "#HKVS_si".
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame. iSplitR "H1 HKVSres".
    - iModIntro. wp_pures.
      wp_apply (aneris_wp_start {[80%positive : port]}).
      iFrame. iSplitR "Hftk1 H2 H5".
      + iModIntro. wp_pures.
        wp_apply (aneris_wp_start {[80%positive : port]}).
        iFrame. iSplitL "HΦ". by iApply "HΦ".
        iIntros "!> Hports". 
        iApply (client_2_spec with "[$]"); done. 
      + iIntros "!> Hports". iApply (client_1_spec with "[$]"); done. 
    - iIntros "!> Hports". wp_apply (server_spec with "[$]"); done.
  Qed.

End proof_runner.

Definition unit_model := model _ (λ _ _, False) ().
Lemma unit_model_rel_finitary : aneris_model_rel_finitary unit_model.
Proof. intros ?. apply finite_smaller_card_nat. apply _. Qed.

Definition ips : gset string :=
  {[ ip_of_address server_addr ; ip_of_address client_1_addr
  ; ip_of_address client_2_addr ]}.

Definition sa_dom : gset socket_address :=
  {[ server_addr ; client_1_addr; client_2_addr]}.

Definition init_state :=
  {|
    state_heaps := {["system" := ∅ ]};
    state_sockets := {["system" := ∅ ]};
    state_ms := ∅;
  |}.
  
  Instance KVS_time_instance
  `{!anerisG Mdl Σ} : KVS_time.
  Proof.
  Admitted.

  Instance SI_init_instance
  `{!anerisG Mdl Σ} : SI_init.
  Proof.
  Admitted.

  Theorem runner_safe :
    aneris_adequate example_runner "system" init_state (λ _, True).
  Proof.
    set (Σ := #[anerisΣ unit_model; KVSΣ]).
    apply (@adequacy Σ unit_model _ _ ips sa_dom ∅ ∅ ∅); try set_solver.
    { apply unit_model_rel_finitary. }
    iIntros (dinvG). iIntros "!> Hunallocated Hhist Hfrag Hips Hlbl _ _ _ _".
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
  Qed. *)