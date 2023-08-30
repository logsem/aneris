From iris.algebra Require Import agree auth excl gmap updates local_updates.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import lang resources resources inject.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.lib.mt_server Require Import user_params.
From aneris.examples.snapshot_isolation.specs Require Import user_params resources.
From aneris.examples.snapshot_isolation.proof
     Require Import time events model.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import
     resource_algebras server_resources proxy_resources global_invariant wrappers.


Section Session_Resources_intantiation.
  Context `{!anerisG Mdl Σ, !IDBG Σ, !MTS_resources}.
  Context `{!User_params}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT : gname).
  Context (srv_si : message → iProp Σ) (SrvInit : iProp Σ).


  Global Program Instance session_resources_instance : SI_resources Mdl Σ :=
    {|
      GlobalInv :=  GlobalInv_def clients γKnownClients γGauth γGsnap γT;
      OwnMemKey k h := OwnMemKey_def γGauth γGsnap k h;
      OwnLocalKey k c vo := ownCacheUser γKnownClients k c vo;
      ConnectionState c s sa := ConnectionState_def γGsnap γKnownClients c s sa;
      IsConnected c sa := is_connected γGsnap γT γKnownClients c sa;
      KeyUpdStatus c k b :=  key_upd_status γKnownClients c k b;
      Seen k h := Seen_def γGsnap k h;
      KVS_si := srv_si;
      KVS_Init := SrvInit;
      KVS_ClientCanConnect sa := client_can_connect_res γKnownClients sa;
      OwnLocalKey_serializable k c v :=
      own_cache_user_serializable γKnownClients k c v;
      (* Seen_valid E k h h' :=  *) |}.
  Next Obligation.
    iIntros (E k h h' Hcl) "#Hinv (#Hs & Hk)".
    iDestruct "Hs" as (hw) "(Hs & %Heq1)".
    iDestruct "Hk" as (hw') "(Hk & %Heq2)".
    unfold OwnMemKey_def, GlobalInv_def.
    iDestruct
      (ownMemSeen_valid clients γKnownClients γGauth γGsnap γT E k hw hw' with
        "[$] [$]")
      as "Hp"; try eauto.
    iMod ("Hp" with "[$Hk]") as "(Hp & %Hpre)".
    iModIntro.
    iSplit; first eauto.
    iPureIntro.
    simplify_eq /=.
    by apply to_hist_prefix_mono.
  Qed.

End Session_Resources_intantiation.
