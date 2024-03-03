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
(* From aneris.examples.transactional_consistency.read_committed.specs
  Require Import resource_algebras resources. *)
From aneris.examples.transactional_consistency Require Import user_params.

Set Default Proof Using "Type".

Section Specification.
  Context `{!anerisG Mdl Σ, !User_params,
            !KVS_transaction_api, !RC_resources Mdl Σ}.

  Definition write_spec : Prop :=
    ∀ (c : val) (sa : socket_address)
      (vo : option val)
      (k : Key) (v : SerializableVal) (b : bool) ,
      ⌜k ∈ KVS_keys⌝ -∗
    {{{ ⌜true⌝ }}}
      TC_write c #k v @[ip_of_address sa] 
    {{{ RET #(); True }}}.
(* 
  Definition read_spec : Prop :=
    ∀ (c : val) (sa : socket_address)
      (k : Key) (vo : option val),
    ⌜k ∈ KVS_keys⌝ -∗
    {{{ true }}}
      TC_read c #k @[ip_of_address sa] 
    {{{ RET $vo; true }}}.

   Definition start_spec : Prop :=
    ∀ (c : val) (sa : socket_address)
       (E : coPset),
      ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (n : nat), true >>>
      TC_start c @[ip_of_address sa] E
    <<<▷ RET #(); true >>>.

  Definition commit_spec : Prop :=
   ∀ (c : val) (sa : socket_address)
     (E : coPset),
     ⌜↑KVS_InvName ⊆ E⌝ -∗
     IsConnected c sa -∗
    <<< ∀∀ (n : nat), true >>>
      TC_commit c @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b; true >>>.

  Definition init_client_proxy_spec : Prop :=
    {{{ true }}}
      TC_init_client_proxy (s_serializer KVS_serialization)
                  #sa #KVS_address @[ip_of_address sa]
    {{{ cstate, RET cstate; true }}}.

  Definition init_kvs_spec : Prop :=
    {{{ true }}}
      TC_init_server (s_serializer KVS_serialization)
        #KVS_address
        @[(ip_of_address KVS_address)]
    {{{ RET #(); True }}}. *)

End Specification.