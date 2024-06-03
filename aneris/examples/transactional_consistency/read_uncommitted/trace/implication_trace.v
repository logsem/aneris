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

  Definition trace_inv_name := nroot.@"trinv".

  (** Ghost theory *)

  (** Wrapped resources  *)
  (* Global Program Instance wrapped_resources `(res : !RU_resources Mdl Σ) : RU_resources Mdl Σ :=
    {|
      GlobalInv := (GlobalInv ∗ trace_inv trace_inv_name valid_trace_ru ∗ ∃ t, trace_is t ∗
                   (∀ c, ⌜latest c t_hist t⌝ ∗ OwnHalfLatest c t_hist))%I;
      OwnMemKey k V := (OwnMemKey k V 
                        ∗ (∀ v, ⌜v ∈ V⌝ → ∃ t tag c, trace_hist t ∗ 
                                ⌜(#(LitString tag), (c, (#"Wr", (#(LitString k), v))))%V ∈ t⌝))%I;
      OwnLocalKey k c vo := (∃ t, OwnLocalKey k c vo ∗ (∀ v, ⌜vo = Some v⌝ → OwnHalfWrite k vo))%I;
      ConnectionState c s sa := (ConnectionState c s sa ∗ 
                                 (∃ t i, trace_hist t_hist ∗ OwnHalfLatest c t_hist ∗
                                         (⌜s = CanStart⌝ ∗ 
                                          (⌜is_cm_post_event (last t_hist)⌝ ∨ ⌜is_st_pre_event (last t_hist)⌝)) ∨ 
                                         (⌜s = (Active dom)⌝ ∗ 
                                          (∃) ∗
                                          (∀ k, ⌜latest_write k vo t_hist⌝ ∗ OwnHalfWrite k vo))))%I;
      IsConnected c sa := IsConnected c sa%I;
      KVS_ru := KVS_ru;
      KVS_Init := KVS_Init%I;
      KVS_ClientCanConnect sa := KVS_ClientCanConnect sa%I;
      Seen k V := Seen k V%I;
    |}.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted. *)

  Lemma library_implication `{!anerisG Mdl Σ} (clients : gset socket_address) 
  (lib : KVS_transaction_api) :
    ((RU_spec clients lib) ∗ trace_is [] ∗ trace_inv trace_inv_name valid_trace_ru) ={⊤}=∗ 
    RU_spec clients (KVS_wrapped_api lib).
  Proof.
    iIntros "([%res (Hkeys & Hkvs_init & Hglob_inv & Hcan_conn & 
      (#Hinit_kvs & #Hinit_cli & #Hread & #Hwrite & #Hstart & #Hcom))] & Htr & #Htr_inv)".
  Admitted.
End trace_proof.