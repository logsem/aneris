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
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import specs resources.
From aneris.examples.transactional_consistency Require Import user_params aux_defs state_based_model.

Section trace_proof.
  Context `{!anerisG Mdl Σ, !User_params}.

  (** Wrapped resources  *)
  Global Program Instance wrapped_resources `(res : !SI_resources Mdl Σ) : SI_resources Mdl Σ :=
    {|
      GlobalInv := True%I;
      OwnMemKey k V := True%I;
      OwnLocalKey k c vo := True%I;
      ConnectionState c s sa := True%I;
      IsConnected c sa := True%I;
      KVS_si := KVS_si;
      KVS_Init := True%I;
      KVS_ClientCanConnect sa := True%I;
      KeyUpdStatus v k b := True%I;
      Seen k V := True%I;
    |}.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  (* Library specification on the form required by the trace infrastructure *)
  Definition si_library_spec (clients : gset socket_address) (P0 : iProp Σ) 
  (lib : KVS_transaction_api) : iProp Σ := 
      (P0 -∗ ∃ (res : SI_resources Mdl Σ),
               ([∗ set] k ∈ KVS_keys, k ↦ₖ []) ∗ 
               KVS_Init ∗ 
               GlobalInv ∗
               ([∗ set] sa ∈ clients, KVS_ClientCanConnect sa) ∗
               init_kvs_spec ∗
               init_client_proxy_spec ∗
               read_spec ∗
               write_spec ∗
               start_spec ∗
               commit_spec).

  (* Primary lemma to be used with adequacy *)
  Lemma library_implication (clients : gset socket_address) 
  (N : namespace) (P0 : iProp Σ) (lib : KVS_transaction_api) :
    si_library_spec clients P0 lib -∗
    si_library_spec clients (P0 ∗ trace_is [] ∗ trace_inv N valid_trace_si) 
                            (KVS_wrapped_api lib).
  Proof.
  Admitted.

End trace_proof.