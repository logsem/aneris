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
     Require Import resource_algebras server_resources proxy_resources
     global_invariant.


Section Session_Resources_intantiation.
  Context `{!anerisG Mdl Σ, !IDBG Σ, !MTS_resources}.
  Context `{!User_params}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT : gname).
  Context (srv_si : message → iProp Σ) (SrvInit : iProp Σ).

  Definition to_hist (h : list write_event) : list val := (λ e, e.(we_val)) <$> h.

  Definition to_local_state (s : proxy_state) : local_state :=
    match s with
      PSCanStart => CanStart
    | PSActive m => Active ((λ h, to_hist h) <$> m)
    end.

  Lemma to_hist_prefix_mono hw hw' :
    hw `suffix_of` hw' →  to_hist hw `suffix_of` to_hist hw'.
  Proof.
  Admitted.

  Definition GlobalInv_def : iProp Σ :=
    Global_Inv clients γKnownClients γGauth γGsnap γT.

  Definition OwnMemKey_def k h : iProp Σ :=
    ∃ hw, ownMemUser γGauth γGsnap k hw ∗ ⌜h = to_hist hw⌝.

  Definition ConnectionState_def c s : iProp Σ :=
    ∃ sp, connection_state  γGsnap γT γKnownClients c sp ∗ ⌜s = to_local_state sp⌝.

  Definition Seen_def k h : iProp Σ :=
    ∃ hw, ownMemSeen γGsnap k hw ∗ ⌜h = to_hist hw⌝.


  Global Program Instance session_resources_instance : SI_resources Mdl Σ :=
    {|
      GlobalInv :=  GlobalInv_def;
      OwnMemKey k h := OwnMemKey_def k h;
      OwnLocalKey k c vo := ownCacheUser γKnownClients k c vo;
      ConnectionState c s := ConnectionState_def c s;
      IsConnected c := is_connected γGsnap γT γKnownClients c;
      KeyUpdStatus c k b :=  key_upd_status γKnownClients c k b;
      Seen k h := Seen_def k h;
      KVS_si := srv_si;
      KVS_Init := SrvInit;
      KVS_ClientCanConnect sa := client_can_connect γKnownClients sa;
      OwnLocalKey_serializable k c v :=
      own_cache_user_serializable γGsnap γT γKnownClients k c v;
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
    (** FixMe in either in the resources or in resources definition. *)
    admit.
    Admitted.

End Session_Resources_intantiation.
