From iris.algebra Require Import auth gmap dfrac frac_auth excl csum.
From iris.algebra.lib Require Import mono_list.
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

Section Read_Proof.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params clients γKnownClients γGauth γGsnap γT).
  Import snapshot_isolation_code_api.


 Definition read_spec_internal {MTR : MTS_resources} : iProp Σ :=
    ∀ (c : val) (sa : socket_address)
      (k : Key) (vo : option val),
    ⌜k ∈ KVS_keys⌝ -∗
    @make_request_spec _ _ _ _ MTC _ -∗
    {{{ is_connected γGsnap γT γKnownClients c sa ∗
        ownCacheUser γKnownClients k c vo }}}
      SI_read c #k @[ip_of_address sa]
    {{{ RET $vo; ownCacheUser γKnownClients k c vo }}}.


  Lemma read_spec_internal_holds {MTR : MTS_resources}  :
    ⊢ read_spec_internal.
  Proof.
    iIntros (c sa k vo Hk) "#Hspec !#".
    iIntros (Φ) "(#Hisc & Hcache) Hpost".
    iDestruct "Hisc" as (lk cst l sv s) "Hisc".
    iDestruct "Hisc" as (γCst γlk γS γA γCache ->) "#(Hc1 & Hisc)".
    rewrite /SI_read /= /read.
    wp_pures.
    wp_apply (acquire_spec (KVS_InvName.@socket_address_to_str sa)
               with "[$Hisc]").
    iIntros (uu) "(_ & Hlk & Hres)".
    wp_pures.
    iDestruct "Hres"
      as "(Hl & Hcr & [( -> & -> & Hres_abs & Htk) | Hres])".
    { iDestruct "Hcache" as (? ? ? ? ? ? ? ? Heq) "Hcache".
      symmetry in Heq. simplify_eq.
      iDestruct "Hcache" as "(#Hc2 & Helem & %Hval)".
      iDestruct (client_connected_agree γGsnap γT
                  with "[$Hc2][$Hc1]") as "%Heq'".
      simplify_eq /=.
      by iDestruct (ghost_map.ghost_map_lookup
                  with "[$Hres_abs][$Helem]")
                  as "%Habs". }
    iDestruct "Hres"
      as (ts Msnap cuL cuV cuM cM -> -> Hcoh Hvalid)
           "(%Hm & #Hts & #Hsn & HcM & Hauth & Htk)".
    wp_load.
    wp_pures.
    wp_load.
    wp_apply (wp_map_lookup $! Hm).
    admit.
    (* iIntros (v1 Hv1). *)
(*     destruct (cuM !! k) eqn:Hkv1 *)
(*     destruct vo eqn:Hvo. *)

(*     - simplify_eq /=. *)
(*       wp_pures. *)
(*       wp_apply (release_spec with *)
(*                "[$Hisc $Hlk Hl Hcr HcM Hauth Htk] [Hcache Hpost]"). *)
(*     { iFrame "#∗". *)
(*       iRight. *)
(*       iExists ts, Msnap, cuL, _, cuM, cM. *)
(*       iFrame "#∗". *)
(*       iPureIntro. *)
(*       split_and!; eauto. } *)
(*     iNext. *)
(*     iIntros (v1 ->). *)
(*     wp_pures.  *)
(*     destruct v eqn:Hv. *)
(*       -- simplify_eq /=. *)
(*          iApply ("Hpost" with "[Hcache]").       *)
(* } *)
  Admitted.

End Read_Proof.
