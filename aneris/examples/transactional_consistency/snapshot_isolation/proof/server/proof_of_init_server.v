From iris.algebra Require Import auth gmap dfrac frac_auth excl csum.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import list_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params mt_server_code.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.transactional_consistency.snapshot_isolation
     Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  user_params time events aux_defs resource_algebras.
From aneris.examples.transactional_consistency.snapshot_isolation.proof
     Require Import utils model kvs_serialization rpc_user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.resources
     Require Import
     server_resources proxy_resources
     global_invariant local_invariant wrappers.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.server
     Require Import
     proof_of_start_handler
     proof_of_read_handler
     proof_of_commit_handler
     proof_of_client_request_handler.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation
  Require Import snapshot_isolation_api_implementation.


Section Proof_of_init_server.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTrs : gname).
  Context (srv_si : message → iProp Σ) (SrvInit : iProp Σ).
  Notation MTC := (client_handler_rpc_user_params
                     clients γKnownClients γGauth γGsnap γT γTrs).
  Import snapshot_isolation_code_api.


  Definition init_server_spec_internal : Prop :=
    {{{ KVS_address ⤇ srv_si ∗
        Global_Inv clients γKnownClients γGauth γGsnap γT γTrs ∗               (@run_server_spec _ _ _ _ MTC SrvInit srv_si) ∗
        SrvInit ∗
        ownMemAuthLocal γGauth (gset_to_gmap [] KVS_keys) ∗
        ownTimeLocal γT 0 ∗
        KVS_address ⤳ (∅, ∅) ∗
        free_ports (ip_of_address KVS_address) {[port_of_address KVS_address]}
    }}}
      init_server (s_serializer KVS_serialization)
      #KVS_address @[ip_of_address KVS_address]
    {{{ RET #(); True }}}.

  Lemma init_server_spec_internal_holds : init_server_spec_internal.
  Proof.
    iStartProof.
    iIntros (Φ) "(#Hsi & #Hinv & Hspec & HinitRes & 
                   HauthL & HtimeL & Hmh & Hfp) HΦ". 
    rewrite /init_server.
    wp_pures.
    wp_apply (wp_map_empty with "[//]").
    iIntros (kvsV HkvsV).
    wp_alloc kvsL as "HpKvs".
    wp_pures.
    wp_alloc vnumL as "Hvnum".
    wp_pures.
    wp_apply (newlock_spec
                (KVS_InvName .@ "lk") (ip_of_address KVS_address)
                (lkResDef γGauth γT kvsL vnumL)                   
               with "[Hvnum HpKvs HauthL HtimeL]") .
    - iExists (gset_to_gmap [] KVS_keys), ∅, 0%nat, ∅, kvsV.
      iSplit; first done.
      iSplit; first by (iPureIntro; apply kvsl_valid_empty).
      iSplit; last by iFrame.
      iPureIntro. intros k h Hkh.
      by apply lookup_gset_to_gmap_Some in Hkh as (H1 & <-).
    - iIntros (lk γlk) "#HLInv".
      wp_pures.
      wp_apply aneris_wp_fork.
      iSplitL "HΦ"; [iNext; by iApply "HΦ"|].
      rewrite /start_server_processing_clients.
      iNext.
      wp_pures.
      iApply ("Hspec" with "[][$Hmh $Hsi $Hfp $HinitRes]"); last done.
      rewrite /handler_spec.
      iIntros (v1 v2 Ψ) "!> HP HΨ".
      wp_pures.
      by iApply (client_request_handler_spec clients
             with "[$HLInv $HP]").
  Qed.   

End Proof_of_init_server.
