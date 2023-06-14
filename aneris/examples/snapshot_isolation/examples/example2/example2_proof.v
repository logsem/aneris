From aneris.aneris_lang Require Import tactics adequacy proofmode.
From aneris.examples.snapshot_isolation.examples.example2
        Require Import example2_code.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params time events resources specs.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code_api.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.

Section proof_of_code.

  Context (addr : socket_address).

  Local Instance example2_params : User_params :=
    {|
      KVS_address := addr;
      KVS_keys := {["x"; "y"]};
      KVS_InvName := nroot .@ "kvs_inv";
      KVS_serialization := int_serialization;
    |}.

  Context `{!anerisG Mdl Σ, !KVS_time, !KVSG Σ,
            !KVS_snapshot_isolation_api, !SI_resources Mdl Σ}.

  Definition local_inv_def : iProp Σ :=
    ("x" ↦ₖ None ∗ "y" ↦ₖ None) ∨
    (∃ w1 w2, "x" ↦ₖ Some w1 ∗ "y" ↦ₖ Some w2 ∗
              ⌜we_val w1 = #1⌝ ∗ ⌜we_val w2 = #1⌝).

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
    
  Admitted.

  Lemma transaction2_spec cst sa :
    {{{
      local_inv ∗
      ConnectionState cst CanStart
    }}}
      transaction2 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
  Admitted.

  Lemma transaction1_client_spec sa :
    {{{
      unallocated {[sa]} ∗
      KVS_address ⤇ KVS_si ∗
      sa ⤳ (∅, ∅) ∗
      free_ports (ip_of_address sa) {[port_of_address sa]}
    }}}
      transaction1_client #sa #KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
  Admitted.
















End proof_of_code.