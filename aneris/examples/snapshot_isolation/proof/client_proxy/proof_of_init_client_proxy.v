From iris.algebra Require Import auth gmap dfrac frac_auth excl csum.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import list_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params mt_server_code.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params resources specs.
From aneris.examples.snapshot_isolation.proof
     Require Import time events model kvs_serialization rpc_user_params.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import
     resource_algebras server_resources proxy_resources global_invariant wrappers.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.
Section Client_Proxy_Proof.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params clients γKnownClients γGauth γGsnap γT).
  Import snapshot_isolation_code_api.

  Definition init_client_proxy_spec_internal {MTR : MTS_resources} : iProp Σ :=
    ∀ (sa : socket_address),
    {{{ unallocated {[sa]} ∗
        KVS_address ⤇ srv_si ∗
        sa ⤳ (∅, ∅) ∗
        (@api_spec.init_client_proxy_spec _ _ _ _ MTC _ srv_si) ∗
        client_can_connect_res γKnownClients sa ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} }}}
      SI_init_client_proxy (s_serializer KVS_serialization)
                  #sa #KVS_address @[ip_of_address sa]
    {{{ cstate, RET cstate;
        ConnectionState_def γKnownClients γGsnap γT cstate CanStart ∗
        is_connected γGsnap γT γKnownClients cstate }}}.

  Lemma init_client_leader_proxy_internal_holds {MTR : MTS_resources}  :
     ⊢ init_client_proxy_spec_internal.
  Proof.
    iIntros (sa Φ) "!#".
    iIntros "(Hf & #Hsi & Hmh & #Hspec & Hcc & Hfp) HΦ".
    rewrite /SI_init_client_proxy /=.
    rewrite /init_client_proxy.
    wp_pures.
    wp_apply ("Hspec" with "[$Hf $Hfp $Hmh $Hsi][Hcc HΦ]").
    iNext.
    iIntros (reqh) "Hreq".
    wp_pures.
    wp_alloc l as "Hl".
    wp_pures.
    iMod (own_alloc (Excl ())) as (γS) "Hs"; first done.
    iMod (own_alloc (Excl ())) as (γA) "Ha"; first done.
    iMod ghost_map.ghost_map_alloc_empty as (γCache) "HCache".
    iDestruct "Hcc" as (γCst) "(#Hcc & Hp)".
    wp_apply (newlock_spec
                (KVS_InvName.@socket_address_to_str sa) _
                (is_connected_def γGsnap γT (ip_of_address sa) reqh l PSCanStart (InjLV #()) γS γA γCache)
               with "[Hreq Hl HCache Hs]").
    - iFrame. iLeft. by iFrame.
    - iIntros (lk γ) "#Hlk".
      iMod (own_update _ _ (Cinr (to_agree (γA, γS, γ, γCache))) with "Hp") as "#Hdefined".
      {  intros n [f |]; simpl; eauto.
         destruct f; simpl; try by inversion 1. }
      wp_pures.
      iApply "HΦ".
      iAssert (is_connected γGsnap γT γKnownClients (#sa, (lk, (reqh, #l)))) as "#Hic".
      iExists _, _, _, _, _, _, _, _.
      iExists _, _, _.
      by iFrame "#∗".
      rewrite /ConnectionState_def /connection_state.
      iFrame "#∗".
      iExists PSCanStart; iSplit; last done.
      iExists sa, (lk, (reqh, #l))%V, γCst, γA, γS, γ, γCache.
      by iFrame "#∗".
  Qed.

End Client_Proxy_Proof.
