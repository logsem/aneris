From aneris.aneris_lang Require Import tactics adequacy proofmode.
From aneris.examples.snapshot_isolation.examples.example2
        Require Import example2_code.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params time events resources specs.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code_api.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.snapshot_isolation.instantiation
      Require Import snapshot_isolation_api_implementation.
Import ser_inj.

Section proof_of_code.

  Context (addr : socket_address).

  Local Instance example2_params : User_params :=
    {|
      KVS_address := addr;
      KVS_keys := {["x"; "y"]};
      KVS_InvName := nroot .@ "kvs_inv";
      KVS_serialization := int_serialization;
      KVS_ser_inj := int_ser_is_ser_injective;
      KVS_ser_inj_alt := int_ser_is_ser_injective_alt
    |}.

  Context `{!anerisG Mdl Σ, !KVS_time, !KVSG Σ, !SI_resources Mdl Σ}.

  Definition local_inv_def : iProp Σ :=
    ∃ vx vy, "x" ↦ₖ vx ∗ "y" ↦ₖ vy ∗
        (⌜is_Some vx⌝ -∗ ∃ w, ⌜vy = Some w⌝ ∗ ⌜we_val w = #1⌝).

  Definition N := nroot .@ "example".

  Definition local_inv := inv N local_inv_def.

  Lemma transaction1_spec cst sa :
    {{{
      local_inv ∗
      ConnectionState cst CanStart ∗
      start_spec ∗
      write_spec ∗
      commit_spec
    }}}
      transaction1 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#inv & CanStart & #start & #write & #commit) HΦ".
    rewrite/transaction1.
    wp_pures.
    wp_apply ("start" $! _ _ (⊤ ∖ ↑N)); first solve_ndisj.
    iInv "inv" as ">(%vx & %vy & x_vx & y_vy & vx_some)" "Hclose".
    iModIntro.
    iExists {["x":=vx; "y":=vy]}.
    iSplitL "CanStart x_vx y_vy"; first iFrame.
    {
      iApply (big_sepM_insert _ _ "x"); [done|iFrame].
      iApply (big_sepM_insert _ _ "y"); by [|iFrame].
    }
    iIntros "!>(active & kv_state & snap)".
    iPoseProof (big_sepM_insert _ _ "x" with "kv_state")
              as "(x_vx & kv_state)"; first done.
    iPoseProof (big_sepM_insert _ _ "y" with "kv_state")
              as "(y_vy & _)"; first done.
    iMod ("Hclose" with "[vx_some x_vx y_vy]").
    { iNext. iExists vx, vy. iFrame. }
    iModIntro.
    wp_pures.
    iPoseProof (big_sepM_insert _ _ "x" with "snap")
              as "(x_vx & snap)"; first done.
    iPoseProof (big_sepM_insert _ _ "y" with "snap")
              as "(y_vy & _)"; first done.
    wp_apply ("write" $! _ _ _ _ (SerVal #1) with "[] x_vx");
            first done.
    iIntros "x_1".
    wp_pures.
    wp_apply ("write" $! _ _ _ _ (SerVal #1) with "[] y_vy");
            first done.
    iIntros "y_1".
    wp_pures.
    (* TODO wait for commitT_spec to be defined *)
  Admitted.

  Lemma transaction2_spec cst sa :
    {{{
      local_inv ∗
      ConnectionState cst CanStart ∗
      start_spec ∗
      read_spec ∗
      commit_spec
    }}}
      transaction2 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#inv & CanStart & #start & #read & #commit) HΦ".
    rewrite/transaction2.
    wp_pures.
    wp_apply ("start" $! _ _ (⊤ ∖ ↑N)); first solve_ndisj.
    iInv "inv" as ">(%vx & %vy & x_vx & y_vy & %vx_some)" "Hclose".
    iModIntro.
    iExists {["x":=vx; "y":=vy]}.
    iSplitL "x_vx y_vy CanStart"; first iFrame.
    {
      iApply (big_sepM_insert _ _ "x"); [done|iFrame].
      iApply (big_sepM_insert _ _ "y"); by [|iFrame].
    }
    iIntros "!>(active & kv_state & snap)".
    iPoseProof (big_sepM_insert _ _ "x" with "kv_state")
              as "(x_vx & kv_state)"; first done.
    iPoseProof (big_sepM_insert _ _ "y" with "kv_state")
              as "(y_vy & _)"; first done.
    iMod ("Hclose" with "[x_vx y_vy]").
    { iNext. iExists vx, vy. by iFrame. }
    iModIntro.
    wp_pures.
    (* TODO wait for wait_on_keyT_spec to be defined *)
  Admitted.

  Lemma transaction1_client_spec sa :
    {{{
      local_inv ∗
      unallocated {[sa]} ∗
      KVS_address ⤇ KVS_si ∗
      sa ⤳ (∅, ∅) ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      init_client_proxy_spec ∗
      start_spec ∗
      write_spec ∗
      commit_spec
    }}}
      transaction1_client #sa #KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#inv & unalloc & #KVS_si & ∅ & free & #init & #start & #write &
                  #commit) HΦ".
    rewrite/transaction1_client.
    wp_pures.
    wp_apply ("init" with "[$unalloc $∅ $free $KVS_si]").
    iIntros (cst) "CanStart".
    wp_pures.
    by wp_apply (transaction1_spec with "[$inv $start $write $commit $CanStart]").
  Qed.

  Lemma transaction2_client_spec sa :
    {{{
      local_inv ∗
      unallocated {[sa]} ∗
      KVS_address ⤇ KVS_si ∗
      sa ⤳ (∅, ∅) ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      init_client_proxy_spec ∗
      start_spec ∗
      read_spec ∗
      commit_spec
    }}}
      transaction2_client #sa #KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#inv & unalloc & #KVS_si & ∅ & free & #init & #start & #read &
                  #commit) HΦ".
    rewrite/transaction2_client.
    wp_pures.
    wp_apply ("init" with "[$unalloc $∅ $free $KVS_si]").
    iIntros (cst) "CanStart".
    wp_pures.
    by wp_apply (transaction2_spec with "[$inv $start $read $commit $CanStart]").
  Qed.

End proof_of_code.

(* Concrete parameters *)
Definition addr := SocketAddressInet "0.0.0.0" 80.
Definition clt1 := SocketAddressInet "0.0.0.1" 80.
Definition clt2 := SocketAddressInet "0.0.0.2" 80.

Definition addresses : gset socket_address := {[addr; clt1; clt2]}.
Definition ips : gset ip_address := {["0.0.0.0"; "0.0.0.1"; "0.0.0.2"]}.

Global Instance params : User_params := example2_params addr.

Definition main : expr :=
  Start "0.0.0.0" (server #KVS_address);;
  Start "0.0.0.1" (transaction1_client #clt1 #KVS_address);;
  Start "0.0.0.2" (transaction1_client #clt2 #KVS_address).

Section proof_of_main.

  Context `{!anerisG Mdl Σ, !KVS_time, !KVSG Σ, !SI_resources Mdl Σ}.

  Lemma main_spec :
    {{{
      local_inv KVS_address ∗
      unallocated {[clt1; clt2]} ∗
      KVS_address ⤇ KVS_si ∗
      KVS_address ⤳ (∅, ∅) ∗
      clt1 ⤳ (∅, ∅) ∗
      clt2 ⤳ (∅, ∅) ∗
      free_ip "0.0.0.0" ∗
      free_ip "0.0.0.1" ∗
      free_ip "0.0.0.2" ∗
      init_client_proxy_spec ∗
      init_kvs_spec ∗
      start_spec ∗
      write_spec ∗
      read_spec ∗
      commit_spec ∗
      KVS_Init
    }}}
      main @["system"]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#inv & unalloc & #KVS_si & KVS_∅ & clt1_∅ & clt2_∅ &
              free_KVS & free_clt1 & free_clt2 & #init_client & #init_kvs &
              #start & #write & #read & #commit & KVS_Init) HΦ".
    rewrite/main.
    wp_apply (aneris_wp_start {[80%positive]} "0.0.0.0").
    iSplitL "free_KVS"; first done.
    iSplitR "KVS_∅ KVS_Init"; last first.
    {
      iIntros "!>free".
      rewrite/server.
      wp_pures.
      by wp_apply ("init_kvs" with "[$KVS_∅ $KVS_Init $free $KVS_si]").
    }
    iNext.
    wp_pures.
  Admitted.


End proof_of_main.