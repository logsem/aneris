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
From aneris.examples.transactional_consistency.snapshot_isolation.examples.sequential_writes
  Require Import sequential_writes_code.
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

Context `{!anerisG Mdl Σ, !SI_resources Mdl Σ, !KVSG Σ}.

  Definition client_inv (γF1 γF2 : gname): iProp Σ :=
    ∃ hx, "x" ↦ₖ hx ∗
    ((⌜hx = [(#1);(#2)]⌝ ∗ token γF1 ∗ token γF2)
    ∨ (⌜hx = [(#1)]⌝ ∗ token γF1)
    ∨ (⌜hx = []⌝)).

  Lemma server_spec ip port :
    ip = ip_of_address KVS_address →
    port = port_of_address KVS_address →
    SI_client_toolbox -∗
    {{{ KVS_Init
      ∗ KVS_address ⤳ (∅, ∅)
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
    server #KVS_address @[ip]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Hip Hports) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (? & ? & ? & ?) HΦ".
    rewrite /server. wp_pures. rewrite Hip Hports.
    by wp_apply ("Hinit_kvs" with "[$]").
  Qed.

  Lemma client_1_spec ip port γF1 γF2:
  ip = ip_of_address client_1_addr →
  port = port_of_address client_1_addr →
  SI_client_toolbox -∗
  {{{ inv client_inv_name (client_inv γF1 γF2)
    ∗ token γF1
    ∗ client_1_addr ⤳ (∅, ∅)
    ∗ unallocated {[client_1_addr]}
    ∗ KVS_ClientCanConnect client_1_addr
    ∗ free_ports ip {[port]}
    ∗ KVS_address ⤇ KVS_si }}}
    transaction1_client $client_1_addr $KVS_address @[ip]
  {{{ v, RET v; True }}}.
  Proof.
    iIntros (Hip Hports) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (#Hinv & Htok & Hmsghis & Hunalloc
    & Hports & Hcc & Hprot) HΦ".
    rewrite /transaction1_client. wp_pures. rewrite Hip Hports.
    wp_apply ("Hinit_cli" with "[$Hunalloc $Hprot $Hmsghis $Hports $Hcc]").
    iIntros (rpc) "(Hcstate & #HiC)". wp_pures. rewrite /transaction1. wp_pures.
    wp_apply ("Hst" $! rpc client_1_addr (⊤ ∖ ↑client_inv_name)); try solve_ndisj.
    iInv (client_inv_name) as ">[%hx [Hkx [(_ & Htok' & _) | [(_ & Htok') | %Heq]]]]" "HClose";
    try iDestruct (token_exclusive with "Htok Htok'") as "[]".
    iModIntro. iFrame.
    iExists {["x" := hx]}.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hkx"; first iFrame.
    iIntros "(Hcstate & [Hkx _] & [Hcx _] & _)".
    iMod ("HClose" with "[Hkx]") as "_".
    { iNext. iExists hx. iFrame. set_solver. }
    iModIntro. wp_pures.
    wp_apply ("Hwr" $! _ _  ⊤ _ (SerVal #1) with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _, _.
    iFrame.
    iIntros "Hcx".
    iModIntro.
    wp_pures.
    wp_apply (commitT_spec rpc client_1_addr (⊤ ∖ ↑client_inv_name));
    try solve_ndisj. iFrame "#".
    iInv (client_inv_name) as ">[%hx' [Hkx [(_ & Htok' & _) | [(_ & Htok') | %Heq']]]]" "HClose";
    try iDestruct (token_exclusive with "Htok Htok'") as "[]".
    iModIntro.
    iExists {["x" := hx']}, _, {["x" := (Some #1, true)]}.
    rewrite Heq Heq'.
    iFrame. iSplitL "Hcx Hkx".
      - iSplitR "Hcx Hkx"; try iSplitR "Hcx Hkx";
        try iPureIntro; try set_solver.
        rewrite !big_sepM_insert; try set_solver.
        rewrite !big_sepM_empty. iFrame.
        iPureIntro. set_solver.
      - iIntros "[_ HBig]".
        iMod ("HClose" with "[HBig Htok]") as "_".
            + iNext. iExists [(#1)].
              rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "HBig" as "[[Hx _] _]".
              iFrame. set_solver.
            + iModIntro. by iApply "HΦ".
  Qed.

  Lemma client_2_spec ip port γF1 γF2:
    ip = ip_of_address client_2_addr →
    port = port_of_address client_2_addr →
    SI_client_toolbox -∗
    {{{ inv client_inv_name (client_inv γF1 γF2)
      ∗ token γF2
      ∗ client_2_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_2_addr]}
      ∗ KVS_ClientCanConnect client_2_addr
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si
      ∗ GlobalInv }}}
      transaction2_client $client_2_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Hip Hports) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (#Hinv & Htok & Hmsghis & Hunalloc
    & Hports & Hcc & Hprot & #ginv) HΦ".
    rewrite /transaction2_client. wp_pures. rewrite Hip Hports.
    wp_apply ("Hinit_cli" with "[$Hunalloc $Hprot $Hmsghis $Hports $Hcc]").
    iIntros (rpc) "(Hcstate & #HiC)". wp_pures. rewrite /transaction2. wp_pures.
    wp_apply (simple_wait_transaction_spec _ _ (#1) "x" _ (⊤ ∖ ↑client_inv_name)
      with "[] [] [$] [] [] [] [$Hcstate $HiC] [HΦ Htok]");
      [solve_ndisj | iPureIntro; set_solver | iFrame "#" | | |].
    - iModIntro.
      iNext.
      iInv (client_inv_name) as ">[%hx' [Hkx Hrest]]" "HClose".
      iModIntro.
      iExists hx'.
      iSplitL "Hkx"; first done.
      iIntros "Hkx".
      iMod ("HClose" with "[Hkx Hrest]") as "_"; last done.
      iNext. iExists _.
      iFrame.
    - iIntros (v Φ') "!>Htrue HΦ".
      wp_lam. wp_op.
      apply bin_op_eval_eq_val.
      case_bool_decide as Heq;
      iApply "HΦ"; set_solver.
    - iIntros (h) "!> (Hcstate & Hseenx)".
      wp_pures.
      wp_apply ("Hst" $! rpc client_2_addr (⊤ ∖ ↑client_inv_name)); try solve_ndisj.
      iInv (client_inv_name) as ">[%hx [Hkx [(_ & _ & Htok') | [ (-> & Htok') | -> ]]]]" "HClose".
      + iDestruct (token_exclusive with "Htok Htok'") as "[]".
      + iModIntro. iFrame.
        iExists {["x" := [(#1)]]}.
        rewrite !big_sepM_insert; try set_solver.
        rewrite big_sepM_empty.
        iSplitL "Hkx"; first iFrame.
        iIntros "(Hcstate & [Hkx _] & [Hcx _] & _)".
        iMod ("HClose" with "[Hkx Htok']") as "_".
        { iNext. iExists [(#1)]. iFrame. set_solver. }
        iModIntro. wp_pures.
        wp_apply ("Hwr" $! _ _  ⊤ _ (SerVal #2) with "[//][][$]"); first set_solver.
        iModIntro.
        iExists _, _.
        iFrame.
        iIntros "Hcx".
        iModIntro.
        wp_pures.
        wp_apply (commitT_spec rpc client_2_addr (⊤ ∖ ↑client_inv_name));
        try solve_ndisj. iFrame "#".
        iInv (client_inv_name) as ">[%hx [Hkx [(_ & _ & Htok') | [ (-> & Htok') | -> ]]]]" "HClose".
        * try iDestruct (token_exclusive with "Htok Htok'") as "[]".
        * iModIntro.
          iExists {["x" := [(#1)]]}, _, {["x" := (Some (#2), true)]}.
          iFrame. iSplitL "Hcx Hkx".
            -- iSplitR "Hcx Hkx"; try iSplitR "Hcx Hkx";
              try iPureIntro; try set_solver.
              rewrite !big_sepM_insert; try set_solver.
              rewrite !big_sepM_empty. iFrame.
            -- iIntros "[_ HBig]".
              iMod ("HClose" with "[HBig Htok Htok']") as "_".
                  ++ iNext. iExists [(#1); (#2)].
                    rewrite !(big_sepM2_insert); try set_solver.
                    iDestruct "HBig" as "[[Hx _] _]".
                    iFrame. iLeft. by iFrame.
                  ++ iModIntro. by iApply "HΦ".
        * iMod (Seen_valid  with "[$ginv][$Hseenx $Hkx]") as "(_ & %Hfalse)";
          first solve_ndisj.
          apply prefix_nil_inv in Hfalse.
          by apply app_nil in Hfalse as [_].
      + iMod (Seen_valid with "[$ginv][$Hseenx $Hkx]") as "(_ & %Hfalse)";
        first solve_ndisj.
        apply prefix_nil_inv in Hfalse.
        by apply app_nil in Hfalse as [_].
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
      ∗ free_ip (ip_of_address client_2_addr) }}}
      example_runner @["system"]
    {{{ v, RET v; True }}}.
  Proof.
    iMod (SI_init_module _ {[client_1_addr; client_2_addr]})
      as (SI_res) "(mem & KVS_Init & #Hginv & Hcc & #specs)";
         first done.
    iMod (own_alloc (Excl ())) as (γF1) "Hftk1"; first done.
    iMod (own_alloc (Excl ())) as (γF2) "Hftk2"; first done.
    iMod (inv_alloc client_inv_name ⊤ (client_inv γF1 γF2) with "[mem]") as "#Hinv".
    { iNext. iExists [].
    iDestruct (big_sepS_delete _ _ "x" with "mem") as "(Hx & HKVSres)";
    first set_solver. iFrame. set_solver.
    }
    iIntros (Φ) "(Hsrvhist & Hcli1hist & Hcli2hist & Hsrvunalloc & Hcli1unalloc
    & Hcli2unalloc & ? & ? & ?) HΦ".
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
    iSplitR "Hsrvhist KVS_Init".
    - iModIntro. wp_pures.
      wp_apply (aneris_wp_start {[80%positive : port]}).
      iFrame.
      iSplitR "Hcli1hist Hcli1unalloc Hftk1 Hcc1".
      + iModIntro. wp_pures.
        wp_apply (aneris_wp_start {[80%positive : port]}).
        iFrame.
        iSplitR "Hcli2hist Hcli2unalloc Hftk2 Hcc2".
        * by iApply "HΦ".
        * iIntros "!> Hports". wp_apply (client_2_spec with "[$][$]"); done.
      + iIntros "!> Hports". wp_apply (client_1_spec with "[$][$]"); done.
    - iIntros "!> Hports". wp_apply (server_spec with "[$][$]"); done.
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
    state_trace := [];
  |}.

Theorem runner_safe :
  aneris_adequate example_runner "system" init_state (λ _, True).
Proof.
  set (Σ := #[anerisΣ unit_model; KVSΣ]).
  apply (@adequacy Σ unit_model _ _ ips sa_dom ∅ ∅ ∅);
    [apply unit_model_rel_finitary| |set_solver..].
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
Qed.
