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

Section trace_proof.
  Context `{!anerisG Mdl Σ, !User_params}.

  (** Wrapped resources  *)
  Global Program Instance wrapped_resources `(res : !RU_resources Mdl Σ) : RU_resources Mdl Σ :=
    {|
      GlobalInv := True%I;
      OwnMemKey k V := True%I;
      OwnLocalKey k c vo := True%I;
      ConnectionState c s sa := True%I;
      IsConnected c sa := True%I;
      KVS_ru := KVS_ru;
      KVS_Init := True%I;
      KVS_ClientCanConnect sa := True%I;
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

  Definition trace_inv_name := nroot.@"trinv".

  (* Primary lemma to be used with adequacy *)
  Lemma library_implication `{!anerisG Mdl Σ} (clients : gset socket_address) 
  (lib : KVS_transaction_api) :
    ((RU_spec clients lib) ∗
    trace_is [] ∗ trace_inv trace_inv_name valid_trace_ru) ={⊤}=∗ 
    RU_spec clients (KVS_wrapped_api lib).
  Proof.
  Admitted.

End trace_proof.