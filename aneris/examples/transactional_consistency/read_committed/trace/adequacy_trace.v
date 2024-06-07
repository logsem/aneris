From aneris.examples.transactional_consistency.read_committed.specs Require Import specs resources.
From aneris.examples.transactional_consistency Require Import state_based_model.
From trillium.prelude Require Import classical_instances.
From trillium.program_logic Require Import language.
From trillium Require Import finitary.
From aneris.aneris_lang Require Import adequacy aneris_lang proofmode adequacy_no_model adequacy_trace.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.transactional_consistency Require Import resource_algebras code_api wrapped_library user_params.
From aneris.examples.transactional_consistency.read_committed.trace Require implication_trace.

Theorem adequacy_trace_rc Σ `{anerisPreG Σ unit_model, KVSG Σ} ip
  (e : expr) (σ : aneris_lang.state) (lib : KVS_transaction_api)
  (U : User_params) (A : gset socket_address) (IPs : gset ip_address) :
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  state_trace σ = [] →
  ip ∉ IPs →
  (∀ `{anerisG Σ}, ⊢ |={⊤}=> RC_spec A lib) →
  (∀ `{anerisG Σ}, ⊢ 
    {{{ RC_spec A (KVS_wrapped_api lib)
        ∗ unallocated A ∗ ([∗ set] a ∈ A, a ⤳ (∅, ∅)) ∗ ([∗ set] ip ∈ IPs, free_ip ip) }}} 
    e @[ip] 
    {{{ v, RET v; True }}}) →
  ∀ σ' e',
    rtc step ([(mkExpr ip e)], σ) (e', σ') →
    valid_trace_rc (state_trace σ').
Proof.
  intros.
  eapply adequacy_trace; try done; first apply valid_trace_rc_empty.
  iIntros (Ag) "(Htr & #Hinv)".
  iMod H5 as "Hspec".
  by iMod (implication_trace.library_implication with "[$Htr $Hspec $Hinv]") 
    as "Hspec".
 Qed.