From iris.algebra Require Import gset auth gmap excl excl_auth csum.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.algebra.lib Require Import mono_list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
  Require Import serialization_proof.
From aneris.examples.reliable_communication.spec
     Require Import ras.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.transactional_consistency
     Require Import code_api.
From aneris.examples.transactional_consistency.read_uncommitted.specs
  Require Import resources aux_defs.
From aneris.examples.transactional_consistency Require Import user_params.

Set Default Proof Using "Type".

Section Specification.
  Context `{!anerisG Mdl Σ, !User_params,
            !KVS_transaction_api, !RU_resources Mdl Σ}.

  Definition write_spec : Prop :=
    ∀ (c : val) (sa : socket_address) (E : coPset) 
      (k : Key) (v : SerializableVal),
      ⌜↑KVS_InvName ⊆ E⌝ -∗
      ⌜k ∈ KVS_keys⌝ -∗
      IsConnected c sa -∗
      <<< ∀∀ (V : Vals) (vo : option val), k ↦ₖ V ∗  k ↦{c} vo >>>
        TC_write c #k v @[ip_of_address sa] E
      <<<▷ RET #(); k ↦ₖ (V ∪ {[Some v.(SV_val)]}) ∗ k ↦{c} Some v.(SV_val) >>>.

  Definition read_spec : Prop :=
    ∀ (c : val) (sa : socket_address) (E : coPset) 
      (k : Key) (v : SerializableVal),
      ⌜↑KVS_InvName ⊆ E⌝ -∗
      ⌜k ∈ KVS_keys⌝ -∗
      IsConnected c sa -∗
    <<< ∀∀ (V : Vals) (vo : option val), k ↦ₖ V ∗  k ↦{c} vo >>>
      TC_read c #k @[ip_of_address sa] E
    <<<▷∃∃ wo, RET $wo; 
      k ↦ₖ V  ∗ k ↦{c} vo ∗ 
      ((⌜vo = None⌝ ∧ ⌜wo ∈ V⌝) ∨ 
      (⌜vo ≠ None⌝ ∧ ⌜wo = vo⌝)) >>>.

  Definition start_spec : Prop :=
    ∀ (c : val) (sa : socket_address) (E : coPset),
      ⌜↑KVS_InvName ⊆ E⌝ -∗
      IsConnected c sa -∗
      <<< ∀∀ (m : gmap Key Vals), 
          ConnectionState c sa CanStart ∗
          [∗ map] k ↦ V ∈ m, k ↦ₖ V >>>
        TC_start c @[ip_of_address sa] E
      <<<▷ RET #(); 
          ConnectionState c sa (Active (dom m)) ∗
          ([∗ map] k ↦ V ∈ m, k ↦ₖ V) ∗
          ([∗ map] k ↦ _ ∈ m, k ↦{c} None) ∗
          ([∗ map] k ↦ V ∈ m, Seen k V) >>>.

  Definition commit_spec : Prop :=
    ∀ (c : val) (sa : socket_address) (E : coPset),
      ⌜↑KVS_InvName ⊆ E⌝ -∗
      IsConnected c sa -∗
      <<< ∀∀ (m : gmap Key Vals) (mc : gmap Key (option val)) 
          (s : gset Key), 
          ConnectionState c sa (Active s) ∗
          ⌜dom m = dom mc⌝ ∗ ⌜dom mc = s⌝ ∗
          ([∗ map] k ↦ V ∈ m, k ↦ₖ V) ∗
          ([∗ map] k ↦ vo ∈ mc, k ↦{c} vo) >>>
        TC_commit c @[ip_of_address sa] E
      <<<▷∃∃ b, RET #b; 
          ConnectionState c sa CanStart ∗
          [∗ map] k ↦ V ∈ m, k ↦ₖ V ∗ Seen k V >>>.

  Definition init_client_proxy_spec : Prop :=
    ∀ (sa : socket_address),
      {{{ unallocated {[sa]} ∗
          KVS_address ⤇ KVS_ru ∗
          sa ⤳ (∅, ∅) ∗
          KVS_ClientCanConnect sa ∗
          free_ports (ip_of_address sa) {[port_of_address sa]} }}}
        TC_init_client_proxy (s_serializer KVS_serialization)
                              #sa #KVS_address @[ip_of_address sa]
      {{{ cstate, RET cstate; ConnectionState cstate sa CanStart ∗
                              IsConnected cstate sa }}}.

  Definition init_kvs_spec : Prop :=
    {{{ KVS_address ⤇ KVS_ru ∗ 
        KVS_address ⤳ (∅,∅) ∗
        free_ports (ip_of_address KVS_address) {[port_of_address KVS_address]} ∗
        KVS_Init }}}
        TC_init_server (s_serializer KVS_serialization)
                        #KVS_address @[(ip_of_address KVS_address)]
      {{{ RET #(); True }}}.

End Specification.