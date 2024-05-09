From iris.algebra Require Import gset auth gmap excl excl_auth csum.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.algebra.lib Require Import mono_list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.transactional_consistency Require Import code_api wrapped_library.
From aneris.examples.transactional_consistency.read_uncommitted.specs Require Import specs resources.
From aneris.examples.transactional_consistency Require Import user_params aux_defs state_based_model.

(** Wrapped resources  *)

(** Library implication *)

Section library_implication.
  Context `{!anerisG Mdl Σ, !User_params}.

  (* Library specification on the form required by the trace infrastructure *)
  Definition ru_library_spec (P0 : iProp Σ) (lib : KVS_transaction_api) 
  (clients : gset socket_address) : iProp Σ :=
    ∃ (res : RU_resources Mdl Σ), 
      □ (P0 -∗ (([∗ set] k ∈ KVS_keys, k ↦ₖ ∅) ∗ KVS_Init ∗ GlobalInv ∗
                ([∗ set] sa ∈ clients, KVS_ClientCanConnect sa))) ∗
      init_kvs_spec ∗
      init_client_proxy_spec ∗
      read_spec ∗
      write_spec ∗
      start_spec ∗
      commit_spec.

  (* Primary lemma to be used with adequacy *)
  Lemma library_implication (N : namespace) (P0 : iProp Σ) 
  (lib : KVS_transaction_api) (clients : gset socket_address) :
    ru_library_spec P0 lib clients -∗
    ru_library_spec (P0 ∗ trace_is [] ∗ trace_inv N valid_ru) 
                    (KVS_wrapped_api lib) clients.
  Proof. 
  Admitted.

End library_implication.

(** Adequacy *)