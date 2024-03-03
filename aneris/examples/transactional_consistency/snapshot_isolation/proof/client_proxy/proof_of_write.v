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
  time events aux_defs resource_algebras.
From aneris.examples.transactional_consistency Require Import user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.proof
     Require Import utils model kvs_serialization rpc_user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.resources
     Require Import
     server_resources proxy_resources global_invariant wrappers.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.

Section Write_Proof.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTrs : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params clients γKnownClients γGauth γGsnap γT γTrs).
  Import code_api.


 Definition write_spec_internal `{!MTS_resources} : Prop :=
    ∀ (c : val) (sa : socket_address)
      (vo : option val)
      (k : Key) (v : SerializableVal) (b : bool),
    ⌜k ∈ KVS_keys⌝ -∗
    {{{ is_connected γGsnap γT γTrs γKnownClients c sa ∗
        ownCacheUser γKnownClients k c vo ∗
        key_upd_status γKnownClients c k b }}}
      TC_write c #k v @[ip_of_address sa]
    {{{ RET #(); ownCacheUser γKnownClients k c (Some v.(SV_val)) ∗
                 key_upd_status γKnownClients c k true }}}.

  Lemma write_spec_internal_holds `{!MTS_resources} : write_spec_internal.
  Proof.
    iIntros (c sa vo k v b Hk Φ) "!# (#Hisc & Hcache & Hkds) Hpost".
    iDestruct "Hisc" as (lk cst l) "Hisc".
    iDestruct "Hisc" as (γCst γlk γS γA γCache γMsnap ->) "#(Hc1 & Hisc)".
    rewrite /TC_write /= /write.
    wp_pures.
    wp_apply (acquire_spec (KVS_InvName.@socket_address_to_str sa)
               with "[$Hisc]").
    iIntros (uu) "(_ & Hlk & Hres)".
    iDestruct "Hres"
      as (?) "(Hl & Hcr & [( -> & Hres_abs & _ & Htk) | Hres])".
    { iDestruct "Hcache" as (? ? ? ? ? ? ? ? ? Heq) "Hcache".
      symmetry in Heq. simplify_eq.
      iDestruct "Hcache" as "(#Hc2 & Helem & %Hval)".
      iDestruct (client_connected_agree with "[$Hc2][$Hc1]") as "%Heq'".
      simplify_eq /=.
      by iDestruct (@ghost_map.ghost_map_lookup
                  with "[$Hres_abs][$Helem]")
                  as "%Habs". }
    iDestruct "Hres"
      as (ts Msnap Msnap_full cuL cuV cuM cM -> Hcoh Hser) "Hres".
    iDestruct "Hres" as (Hvalid)
           "(%Hm & %Hsub & #Hts & #Hsn & #Hf & HcM & Hauth & Htk)".
    wp_pures.
    wp_load.
    wp_pures.
    wp_load.
    wp_apply (wp_map_insert $! Hm).
    iIntros (cuV' Hm').
    wp_store.
    iDestruct "Hcache" as (? ? ? ? ? ? ? ? ? Heq)
                            "(#Hc3 & HcacheHalf1 & %Hv)".
    symmetry in Heq. simplify_eq /=.
    iDestruct (client_connected_agree with "[$Hc3][$Hc1]") as "%Heq'".
    simplify_eq.
    iDestruct "Hkds" as (? ? ? ? ? ? ? ? ? Heq')
                            "(#Hc4 & HcacheHalf2 & %Hb)".
    symmetry in Heq'. simplify_eq /=.
    iDestruct (client_connected_agree with "[$Hc4][$Hc1]") as "%Heq''".
    simplify_eq.
    iDestruct (@ghost_map.ghost_map_elem_combine
                with "[$HcacheHalf1][$HcacheHalf2]") as "(Hcache & ->)".
    rewrite dfrac_op_own Qp.half_half.
    iDestruct (@ghost_map.ghost_map_lookup with
                "[$Hauth][$Hcache]") as "%Hkin".
    iMod (ghost_map.ghost_map_update ((Some v.(SV_val)), true)
           with "[$Hauth][$Hcache]") as "(Hauth & (H1 & H2))".
    wp_apply (release_spec with
               "[$Hisc $Hlk Hl Hcr HcM Hauth Htk] [H1 H2 Hpost]").
    { iExists _.
      iFrame "#∗".
      iRight.
      iExists ts, Msnap, _, cuL, cuV', (<[k:=v.(SV_val)]> cuM),
                (<[k:=(Some v.(SV_val), true)]> cM).
      iFrame "#∗".
      iSplit; first done.
      iSplit.
      { iPureIntro;
          by eapply is_coherent_cache_upd. }
      iSplit; last done.
      iPureIntro.
      apply map_Forall_insert_2; last done.
      apply SV_ser.
    }
    iNext.
    iIntros (v0 ->).
    iApply "Hpost".
    iSplitL "H1".
    { iExists _, _, _, _, _, _, _, _.
      iExists true.
      iSplit; first done.
      iFrame "#∗".
      by destruct v. }
    iExists _, _, _, _, _, _, _, _.
    iExists _.
    iSplit; first done.
    iFrame "#∗".
    eauto.
  Qed.

End Write_Proof.
