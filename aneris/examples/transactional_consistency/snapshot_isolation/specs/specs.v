From iris.algebra Require Import auth gmap excl excl_auth csum.
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
From aneris.examples.transactional_consistency.snapshot_isolation.specs
  Require Import
  time events aux_defs resources.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params.

Set Default Proof Using "Type".

Section Specification.
  Context `{!anerisG Mdl Σ, !User_params,
            !KVS_transaction_api, !SI_resources Mdl Σ}.

  Definition write_spec : iProp Σ :=
    □ ∀ (c : val) (sa : socket_address) (E : coPset)
    (k : Key) (v : SerializableVal),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜k ∈ KVS_keys⌝ -∗
    IsConnected c sa -∗
    <<< ∀∀ (vo : option val) (b : bool), 
      k ↦{c} vo ∗ KeyUpdStatus c k b >>>
      TC_write c #k v @[ip_of_address sa] E
    <<<▷ RET #(); k ↦{c} Some v.(SV_val) ∗ KeyUpdStatus c k true >>>.

  Definition read_spec : iProp Σ :=
    □ ∀ (c : val) (sa : socket_address) (E : coPset)
    (k : Key),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    ⌜k ∈ KVS_keys⌝ -∗
    IsConnected c sa -∗
    <<< ∀∀ (vo : option val), k ↦{c} vo >>>
      TC_read c #k @[ip_of_address sa] E
    <<<▷ RET $vo; k ↦{c} vo >>>.

   Definition start_spec : iProp Σ :=
    □ ∀ (c : val) (sa : socket_address)
    (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    IsConnected c sa -∗
    <<< ∀∀ (m : gmap Key Hist),
      ConnectionState c sa CanStart ∗
      [∗ map] k ↦ h ∈ m, k ↦ₖ h >>>
      TC_start c @[ip_of_address sa] E
    <<<▷ RET #();
      ConnectionState c sa (Active m) ∗
      ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
      ([∗ map] k ↦ h ∈ m, k ↦{c} (last h) ∗ KeyUpdStatus c k false) ∗
      ([∗ map] k ↦ h ∈ m, Seen k h) >>>.

  Definition commit_spec : iProp Σ :=
    □ ∀ (c : val) (sa : socket_address)
    (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    IsConnected c sa -∗
    <<< ∀∀ (m ms: gmap Key Hist) (mc : gmap Key (option val * bool)),
      ConnectionState c sa (Active ms) ∗
      ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
      ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
      ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1  ∗ KeyUpdStatus c k p.2) >>>
      TC_commit c @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
      ConnectionState c sa CanStart ∗
      (** Transaction has been commited. *)
      ((⌜b = true⌝ ∗ ⌜can_commit m ms mc⌝ ∗
        ([∗ map] k↦ h;p ∈ m; mc, k ↦ₖ commit_event p h ∗ Seen k (commit_event p h))) ∨
      (** Transaction has been aborted. *)
      (⌜b = false⌝ ∗ ⌜¬ can_commit m ms mc⌝ ∗
        [∗ map] k ↦ h ∈ m, k ↦ₖ h ∗ Seen k h)) >>>.

  Definition init_client_proxy_spec : iProp Σ :=
    ∀ (sa : socket_address),
    {{{ unallocated {[sa]} ∗
        KVS_address ⤇ KVS_si ∗
        sa ⤳ (∅, ∅) ∗
        KVS_ClientCanConnect sa ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} }}}
      TC_init_client_proxy (s_serializer KVS_serialization)
                  #sa #KVS_address @[ip_of_address sa]
    {{{ cstate, RET cstate; ConnectionState cstate sa CanStart ∗
                            IsConnected cstate sa }}}.

  Definition init_kvs_spec : iProp Σ :=
    {{{ KVS_address ⤇ KVS_si ∗
          KVS_address ⤳ (∅,∅) ∗
          free_ports (ip_of_address KVS_address)
                    {[port_of_address KVS_address]} ∗
        KVS_Init }}}
        TC_init_server (s_serializer KVS_serialization)
          #KVS_address
          @[(ip_of_address KVS_address)]
      {{{ RET #(); True }}}.

End Specification.

Section SI_Module.
  Context `{!anerisG Mdl Σ, !User_params,
            !KVSG Σ, !KVS_transaction_api}.

  Class SI_client_toolbox `{!SI_resources Mdl Σ} := {
    SI_init_kvs_spec : ⊢ init_kvs_spec ;
    SI_init_client_proxy_spec : ⊢ init_client_proxy_spec;
    SI_read_spec : ⊢ read_spec ;
    SI_write_spec : ⊢ write_spec;
    SI_start_spec : ⊢ start_spec;
    SI_commit_spec : ⊢ commit_spec;
  }.
 
   Class SI_init := {
    SI_init_module E (clients : gset socket_address) :
      ↑KVS_InvName ⊆ E →
       ⊢ |={E}=>
      ∃ (res : SI_resources Mdl Σ),
        ([∗ set] k ∈ KVS_keys, k ↦ₖ []) ∗
        KVS_Init ∗
        GlobalInv ∗
        ([∗ set] sa ∈ clients, KVS_ClientCanConnect sa) ∗
        init_kvs_spec ∗
        init_client_proxy_spec ∗
        read_spec ∗
        write_spec ∗
        start_spec ∗
        commit_spec
     }.
   
End SI_Module.