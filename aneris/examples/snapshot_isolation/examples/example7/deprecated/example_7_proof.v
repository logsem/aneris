From aneris.aneris_lang Require Import network resources proofmode.
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
From aneris.examples.snapshot_isolation.examples.example7 Require Import example_7_code.
Import ser_inj.
From aneris.examples.snapshot_isolation.util.util_deprecated Require Import util_proof.

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

Context `{!anerisG Mdl Σ, !KVS_time, !SI_resources Mdl Σ}.

  Definition client_specs : iProp Σ :=
    init_client_proxy_spec ∗ start_spec ∗ read_spec ∗ write_spec ∗ commit_spec.

  Definition client_inv : iProp Σ :=
  (∃ wy wx, "x" ↦ₖ Some wx ∗ "y" ↦ₖ Some wy ∗ ⌜we_val wx = we_val wy ⌝)  
  ∨ ("x" ↦ₖ None ∗ "y" ↦ₖ None).

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

  Lemma transaction ip port client_addr (number : nat) :
  ip = ip_of_address client_addr →
  port = port_of_address client_addr →
  {{{ client_specs
    ∗ inv client_inv_name client_inv
    ∗ client_addr ⤳ (∅, ∅)
    ∗ unallocated {[client_addr]}
    ∗ free_ports ip {[port]}
    ∗ KVS_address ⤇ KVS_si }}}
    transaction $client_addr $KVS_address #number @[ip]
  {{{ v, RET v; True }}}.
Proof.
  iIntros (H1 H2 Φ) "([#HInit [#HStart [#HRead [#HWrite #HCommit]]]] & #Hinv & H3 & H4 & H5 & H6) HΦ" .
    rewrite /transaction. wp_pures. rewrite H1 H2.
    wp_apply ("HInit" with "[$H4 $H6 $H3 $H5]").
    iIntros (rpc) "Hcstate". wp_pures.
    wp_apply ("HStart" $! rpc client_addr (⊤ ∖ ↑client_inv_name)); try solve_ndisj.
    iInv (client_inv_name) as ">HOpen" "HClose".
    iModIntro. iFrame. unfold client_inv.
    iDestruct "HOpen" as "[case1 | case2]".
    - (* Invariant in Some state *)
    iDestruct "case1" as (wy wx) "[Hy [Hx #Heq]]".
    iExists {["x" := Some wx; "y" := Some wy]}.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hy Hx". iFrame.
    iNext. iIntros "(H3 & [H4 [H4' _]] & [H5 H5'] & [H6 H6'] & _)".
    iMod ("HClose" with "[H4 H4']") as "_".
       * iNext. iLeft. iExists wy, wx. by iFrame.
       * iModIntro. wp_pures.
       wp_apply ("HWrite" $! _ _ _ _ (SerVal #number) with "[] [H5 H5']"). 
       set_solver. iFrame. iIntros "(H5 & H5')". wp_pures.
       wp_apply ("HWrite" $! _ _ _ _ (SerVal #number) with "[] [H6 H6']").
       set_solver. iFrame. iIntros "(H6 & H6')". wp_pures.
       wp_apply ("HCommit" $! rpc client_addr (⊤ ∖ ↑client_inv_name));
       try solve_ndisj.
       iInv (client_inv_name) as ">[HOpen | [Hx Hy]]" "HClose"; iModIntro.
        + iDestruct "HOpen" as (wy0 wx0) "[Hx [Hy #Heq']]".
        iExists {["x" := Some wx0; "y" := Some wy0]}, _, 
        {["x" := (Some #number, true); "y" := (Some #number, true)]}.
        iFrame. iSplitL "H5 H5' H6 H6' Hx Hy".
          -- iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
          iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
          iSplitR "H5 H5' H6 H6'".
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
          -- iModIntro.
          iIntros (b) "[HBig [[HBig2 [HBig3 HBig4]] | [HBig1 [HBig2 HBig3]]]]". 
            ++ iMod ("HClose" with "[HBig4]") as "_".
              ** iNext. iLeft. iDestruct "HBig4" as (?) "[? HBig4]".
              iExists {| we_key := "y"; we_val := #number; we_time := t |},
              {| we_key := "x"; we_val := #number; we_time := t |}.
              rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "HBig4" as "[Hx [Hy _]]". by iFrame.
              ** iModIntro. by iApply "HΦ".
            ++ iMod ("HClose" with "[HBig3]") as "_".
              ** iNext. iLeft. iExists wy0, wx0.
              rewrite !big_sepM_insert; try set_solver. 
              iDestruct "HBig3" as "[? [? _]]". by iFrame.
              ** iModIntro. by iApply "HΦ".  
        + iExists {["x" := None; "y" := None]}, _, 
        {["x" := (Some #number, true); "y" := (Some #number, true)]}.
        iFrame. iSplitL "H5 H5' H6 H6' Hx Hy".
          -- iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
          iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
          iSplitR "H5 H5' H6 H6'".
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
          -- iModIntro. iIntros (b) "[HBig [[HBig2 [HBig3 HBig4]] | [HBig1 [HBig2 HBig3]]]]".
            ++ iMod ("HClose" with "[HBig4]") as "_".
              ** iNext. iLeft. iDestruct "HBig4" as (?) "[? HBig4]".
              iExists {| we_key := "y"; we_val := #number; we_time := t |},
              {| we_key := "x"; we_val := #number; we_time := t |}.
              rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "HBig4" as "[Hx [Hy _]]". by iFrame.
              ** iModIntro. by iApply "HΦ".
            ++ iMod ("HClose" with "[HBig3]") as "_".
              ** iNext. iRight. rewrite !big_sepM_insert; try set_solver. 
              iDestruct "HBig3" as "[? [? _]]". by iFrame.
              ** iModIntro. by iApply "HΦ". 
    - (* Invariant in None state *) 
    iDestruct "case2" as "[Hy Hx]".
    iExists {["x" := None; "y" := None]}.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hy Hx". iFrame.
    iNext. iIntros "(H3 & [H4 [H4' _]] & [H5 H5'] & [H6 H6'] & _)".
    iMod ("HClose" with "[H4 H4']") as "_".
       * iNext. iRight. iFrame.
       * iModIntro. wp_pures.
       wp_apply ("HWrite" $! _ _ _ _ (SerVal #number) with "[] [H5 H5']"). 
       set_solver. iFrame. iIntros "(H5 & H5')". wp_pures.
       wp_apply ("HWrite" $! _ _ _ _ (SerVal #number) with "[] [H6 H6']").
       set_solver. iFrame. iIntros "(H6 & H6')". wp_pures.
       wp_apply ("HCommit" $! rpc client_addr (⊤ ∖ ↑client_inv_name));
       try solve_ndisj.
       iInv (client_inv_name) as ">[HOpen | [Hx Hy]]" "HClose"; iModIntro.
        + iDestruct "HOpen" as (wy0 wx0) "[Hx [Hy #Heq']]".
        iExists {["x" := Some wx0; "y" := Some wy0]}, _, 
        {["x" := (Some #number, true); "y" := (Some #number, true)]}.
        iFrame. iSplitL "H5 H5' H6 H6' Hx Hy".
          -- iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
          iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
          iSplitR "H5 H5' H6 H6'".
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
          -- iModIntro. iIntros (b) "[HBig [[HBig2 [HBig3 HBig4]] | [HBig1 [HBig2 HBig3]]]]".
            ++ iMod ("HClose" with "[HBig4]") as "_".
              ** iNext. iLeft. iDestruct "HBig4" as (?) "[? HBig4]".
              iExists {| we_key := "y"; we_val := #number; we_time := t |},
              {| we_key := "x"; we_val := #number; we_time := t |}.
              rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "HBig4" as "[Hx [Hy _]]". by iFrame.
              ** iModIntro. by iApply "HΦ".
            ++ iMod ("HClose" with "[HBig3]") as "_".
              ** iNext. iLeft. iExists wy0, wx0.
              rewrite !big_sepM_insert; try set_solver. 
              iDestruct "HBig3" as "[? [? _]]". by iFrame.
              ** iModIntro. by iApply "HΦ".  
        + iExists {["x" := None; "y" := None]}, _, 
        {["x" := (Some #number, true); "y" := (Some #number, true)]}.
        iFrame. iSplitL "H5 H5' H6 H6' Hx Hy".
          -- iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
          iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
          iSplitR "H5 H5' H6 H6'".
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
          -- iModIntro. iIntros (b) "[HBig [[HBig2 [HBig3 HBig4]] | [HBig1 [HBig2 HBig3]]]]".
            ++ iMod ("HClose" with "[HBig4]") as "_".
              ** iNext. iLeft. iDestruct "HBig4" as (?) "[? HBig4]".
              iExists {| we_key := "y"; we_val := #number; we_time := t |},
              {| we_key := "x"; we_val := #number; we_time := t |}.
              rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "HBig4" as "[Hx [Hy _]]". by iFrame.
              ** iModIntro. by iApply "HΦ".
            ++ iMod ("HClose" with "[HBig3]") as "_".
              ** iNext. iRight. rewrite !big_sepM_insert; try set_solver. 
              iDestruct "HBig3" as "[? [? _]]". by iFrame.
              ** iModIntro. by iApply "HΦ". 
  Qed.

  Lemma client_1_spec ip port :
    ip = ip_of_address client_1_addr →
    port = port_of_address client_1_addr →
    {{{ client_specs
      ∗ inv client_inv_name client_inv
      ∗ client_1_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_1_addr]}
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      client_1 $client_1_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (H1 H2 Φ) "([#HInit [#HStart [#HRead [#HWrite #HCommit]]]] & #Hinv & H3 & H4 & H5 & H6) HΦ".
    rewrite /client_1. wp_pures.
    wp_apply (transaction ip port client_1_addr 1 with "[$]"); try done.
  Qed.

  Lemma client_2_spec ip port :
    ip = ip_of_address client_2_addr →
    port = port_of_address client_2_addr →
    {{{ client_specs 
      ∗ inv client_inv_name client_inv
      ∗ client_2_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_2_addr]}
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      client_2 $client_2_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (H1 H2 Φ) "([#HInit [#HStart [#HRead [#HWrite #HCommit]]]] & #Hinv & H3 & H4 & H5 & H6) HΦ".
    rewrite /client_2. wp_pures.
    wp_apply (transaction ip port client_2_addr 2 with "[$]"); try done.
  Qed.

  Lemma client_3_spec ip port client_3_addr :
    ip = ip_of_address client_3_addr →
    port = port_of_address client_3_addr →
    {{{ client_specs
      ∗ inv client_inv_name client_inv
      ∗ client_3_addr ⤳ (∅, ∅)
      ∗ unallocated {[client_3_addr]}
      ∗ free_ports ip {[port]}
      ∗ KVS_address ⤇ KVS_si }}}
      client_3 $client_3_addr $KVS_address @[ip]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (H1 H2 Φ) "([#HInit [#HStart [#HRead [#HWrite #HCommit]]]] & #Hinv & H3 & H4 & H5 & H6) HΦ" .
    rewrite /client_3. wp_pures.
    rewrite H1. rewrite H2.
    wp_apply ("HInit" with "[$H4 $H6 $H3 $H5]").
    iIntros (rpc) "Hcstate". wp_pures. rewrite /client_3. wp_pures.
    wp_apply ("HStart" $! rpc client_3_addr (⊤ ∖ ↑client_inv_name));
    try solve_ndisj.
    iInv (client_inv_name) as ">HOpen" "HClose".
    iModIntro. iFrame.
    iDestruct "HOpen" as "[case1 | [Hx Hy]]".
    - (* Invariant in Some state *) 
      iDestruct "case1" as (wy wx) "[Hy [Hx %Heq]]".
      iExists {["x" := Some wx; "y" := Some wy]}.
      rewrite !big_sepM_insert; try set_solver.
      rewrite big_sepM_empty.
      iSplitL "Hy Hx". iFrame.
      iNext. iIntros "(H3 & [H4 [H4' _]] & [H5 H5'] & [H6 H6'] & _)".
      iMod ("HClose" with "[H4 H4']") as "_".
        * iNext. iLeft. iExists wy, wx. by iFrame.
        * iModIntro. wp_pures. 
        wp_apply ("HRead" $! _ _ _ _ with "[] [H5]"); try set_solver.
        iFrame. iIntros "H5". wp_pures.
        wp_apply ("HRead" $! _ _ _ _ with "[] [H6]"); try set_solver.
        iFrame. iIntros "H6". wp_pures. 
        (* wp_apply (commitT_spec _ _ (⊤ ∖ ↑client_inv_name) with "[] [] [HΦ H3 H5' H6' H5 H6]");
        try solve_ndisj.
        iInv (client_inv_name) as ">[HOpen | [Hx Hy]]" "HClose"; iModIntro.
          + iDestruct "HOpen" as (wy0 wx0) "[Hx [Hy #Heq']]".
          iExists {["x" := Some wx0; "y" := Some wy0]}, 
          {["x" := Some wx; "y" := Some wy]}, 
          {["x" := (Some (we_val wx), false); "y" := (Some (we_val wy), false)]}.
          iFrame. iSplitL "H5 H5' H6 H6' Hx Hy".
            --  iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. 
            { unfold can_commit. intros. 
            destruct (decide (k = "x")). simplify_eq.
            destruct (decide (k = "y")). simplify_eq.
            simplify_map_eq. } 
            iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
            iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
            iSplitR "H5 H5' H6 H6'".
            rewrite !big_sepM_insert; try set_solver.
            rewrite !big_sepM_empty. iFrame.
            rewrite !big_sepM_insert; try set_solver.
            rewrite !big_sepM_empty. simpl. iFrame.
            -- iModIntro. iIntros "[HBig1 HBig2]".
            iDestruct "HBig2" as (t) "[HBig2 HBig2']".
            iMod ("HClose" with "[HBig2']") as "_".
              ** iNext. iLeft. iExists _, _.
              rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "HBig2'" as "[Hx [Hy _]]". by iFrame.
              ** iModIntro. rewrite Heq. wp_pures. wp_lam. wp_pures.
              case_bool_decide as Heq'; try set_solver.
              wp_pures. by iApply "HΦ".
          + iExists {["x" := None; "y" := None]}, 
          {["x" := Some wx; "y" := Some wy]}, 
          {["x" := (Some (we_val wx), false); "y" := (Some (we_val wy), false)]}.
          iFrame. iSplitL "H5 H5' H6 H6' Hx Hy".
            --  iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. 
            { unfold can_commit. intros. 
            destruct (decide (k = "x")). simplify_eq.
            destruct (decide (k = "y")). simplify_eq.
            simplify_map_eq. } 
            iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
            iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
            iSplitR "H5 H5' H6 H6'".
            rewrite !big_sepM_insert; try set_solver.
            rewrite !big_sepM_empty. iFrame.
            rewrite !big_sepM_insert; try set_solver.
            rewrite !big_sepM_empty. iFrame.
            -- iModIntro. iIntros "[HBig1 HBig2]".
            iDestruct "HBig2" as (t) "[HBig2 HBig2']".
            iMod ("HClose" with "[HBig2']") as "_".
              ++ iNext. iRight.
              rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "HBig2'" as "[Hx [Hy _]]". by iFrame.
              ++ iModIntro. rewrite Heq. wp_pures. wp_lam. wp_pures.
              case_bool_decide as Heq'; try set_solver.
              wp_pures. by iApply "HΦ".
    - (* Invariant in None state *)
    iExists {["x" := None; "y" := None]}.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hy Hx". iFrame.
    iNext. iIntros "(H3 & [H4 [H4' _]] & [H5 H5'] & [H6 H6'] & _)".
    iMod ("HClose" with "[H4 H4']") as "_".
       * iNext. iRight. by iFrame.
       * iModIntro. wp_pures.
       wp_apply ("HRead" $! _ _ _ _ with "[] [H5]"); try set_solver.
       iFrame. iIntros "H5". wp_pures.
       wp_apply ("HRead" $! _ _ _ _ with "[] [H6]"); try set_solver.
       iFrame. iIntros "H6". wp_pures.
       wp_apply (commitT_spec _ _ (⊤ ∖ ↑client_inv_name) with "[] [] [HΦ H3 H5' H6' H5 H6]");
       try solve_ndisj.
       iInv (client_inv_name) as ">[HOpen | [Hx Hy]]" "HClose"; iModIntro.
          + iDestruct "HOpen" as (wy0 wx0) "[Hx [Hy #Heq']]".
          iExists {["x" := Some wx0; "y" := Some wy0]}, 
          {["x" := None; "y" := None]}, 
          {["x" := (None, false); "y" := (None, false)]}.
          iFrame. iSplitL "H5 H5' H6 H6' Hx Hy".
            -- iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. 
            { unfold can_commit. intros. 
            destruct (decide (k = "x")). simplify_eq.
            destruct (decide (k = "y")). simplify_eq.
            simplify_map_eq. } 
            iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
            iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
            iSplitR "H5 H5' H6 H6'".
            rewrite !big_sepM_insert; try set_solver.
            rewrite !big_sepM_empty. iFrame.
            rewrite !big_sepM_insert; try set_solver.
            rewrite !big_sepM_empty. iFrame.
            -- iModIntro. iIntros "[HBig1 HBig2]".
            iDestruct "HBig2" as (t) "[HBig2 HBig2']".
            iMod ("HClose" with "[HBig2']") as "_".
                ** iNext. iLeft. iExists _, _.
                rewrite !(big_sepM2_insert); try set_solver.
                iDestruct "HBig2'" as "[Hx [Hy _]]". by iFrame.
                ** iModIntro. wp_pures. wp_lam. wp_pures.
                by iApply "HΦ".
          + iExists {["x" := None; "y" := None]}, 
          {["x" := None; "y" := None]}, 
          {["x" := (None, false); "y" := (None, false)]}.
          iFrame. iSplitL "H5 H5' H6 H6' Hx Hy".
            -- iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. 
            { unfold can_commit. intros. set_solver. } 
            iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
            iSplitR "H5 H5' H6 H6' Hx Hy". iPureIntro. set_solver.
            iSplitR "H5 H5' H6 H6'".
            rewrite !big_sepM_insert; try set_solver.
            rewrite !big_sepM_empty. iFrame.
            rewrite !big_sepM_insert; try set_solver.
            rewrite !big_sepM_empty. simpl. iFrame.
            -- iModIntro. iIntros "[HBig1 HBig2]".
            iDestruct "HBig2" as (t) "[HBig2 HBig2']".
            iMod ("HClose" with "[HBig2']") as "_".
              ++ iNext. iRight.
              rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "HBig2'" as "[Hx [Hy _]]". by iFrame.
              ++ iModIntro. wp_pures. wp_lam. wp_pures.
              by iApply "HΦ". *)
  Admitted.
  
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
    iMod (SI_init_module $! (I: True)) as (SIres) "(#H1' & H2' & #H3' & HKVSres & #H4' & [#H9' [#H10' [#H11' [#H12' H13]]]])".
    iMod (inv_alloc client_inv_name ⊤ (client_inv) with "[H2']") as "#Hinv".
    { iModIntro. unfold client_inv. iRight.
    iDestruct (big_sepS_delete _ _ "x" with "H2'") as "(Hx & H2')";
    first set_solver.
    iDestruct (big_sepS_delete _ _ "y" with "H2'") as "(Hy & H2')";
    first set_solver. iFrame.
    }
    iIntros (Φ) "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10
    & H11 & H12) HΦ".
    rewrite /example_runner.
    wp_pures.
    wp_apply (aneris_wp_socket_interp_alloc_singleton KVS_si with "H5").
    iIntros "#HKVS_si".
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "H1 HKVSres".
    - iModIntro. wp_pures.
      wp_apply (aneris_wp_start {[80%positive : port]}).
      iFrame.
      iSplitR "H2 H6".
      + iModIntro. wp_pures.
        wp_apply (aneris_wp_start {[80%positive : port]}).
        iFrame.
        iSplitR "H3 H7".
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

Instance KVS_time_instance
`{!anerisG Mdl Σ} : KVS_time.
Proof.
Admitted.

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