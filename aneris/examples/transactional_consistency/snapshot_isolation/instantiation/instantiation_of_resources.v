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
From aneris.examples.reliable_communication.lib.mt_server.spec Require Import api_spec.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  time events aux_defs resources.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.proof
     Require Import utils model.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.resources
     Require Import
     server_resources proxy_resources global_invariant wrappers.


Section SI_Resources_intantiation.
  Context `{!anerisG Mdl Σ, !IDBG Σ, !MTS_user_params, !MTS_resources}.
  Context `{!User_params}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTrs : gname).
  Context (srv_si : message → iProp Σ) (SrvInit : iProp Σ).


  Global Program Instance SI_resources_instance : SI_resources Mdl Σ :=
    {|
      GlobalInv :=  GlobalInv_def clients γKnownClients γGauth γGsnap γT γTrs;
      OwnMemKey k h := OwnMemKey_def γGauth γGsnap k h;
      OwnLocalKey k c vo := ownCacheUser γKnownClients k c vo;
      ConnectionState c s sa :=
        ConnectionState_def γKnownClients γGsnap c s sa;
      IsConnected c sa :=
        (GlobalInv_def clients γKnownClients γGauth γGsnap γT γTrs ∗
        make_request_spec ∗
        is_connected γGsnap γT γTrs γKnownClients c sa)%I;
      KeyUpdStatus c k b :=  key_upd_status γKnownClients c k b;
      Seen k h := Seen_def γGsnap k h;
      KVS_si := srv_si;
      KVS_Init :=
        (SrvInit ∗ 
         api_spec.run_server_spec SrvInit srv_si ∗
         GlobalInv_def clients γKnownClients γGauth γGsnap γT γTrs ∗
         ghost_map_auth γGauth (1 / 2) (gset_to_gmap [] KVS_keys) ∗
         mono_nat_auth_own γT (1 / 2) 0);
      KVS_ClientCanConnect sa :=
        (api_spec.init_client_proxy_spec srv_si ∗
         client_can_connect_res γKnownClients sa ∗
         GlobalInv_def clients γKnownClients γGauth γGsnap γT γTrs ∗
         make_request_spec
        )%I;
      OwnLocalKey_serializable k c v :=
      own_cache_user_serializable γKnownClients k c v;
      (* Seen_valid E k h h' :=  *) |}.
  Next Obligation.
    iIntros (E k h h' Hcl) "#Hinv (#Hs & Hk)".
    iDestruct "Hs" as (hw) "(Hs & %Heq1)".
    iDestruct "Hk" as (hw') "(Hk & %Heq2)".
    unfold OwnMemKey_def, GlobalInv_def.
    iDestruct
      (ownMemSeen_valid clients γKnownClients γGauth γGsnap γT γTrs E k hw hw' with
        "[$] [$]")
      as "Hp"; try eauto.
    iMod ("Hp" with "[$Hk]") as "(Hp & %Hpre)".
    iModIntro.
    iSplit; first eauto.
    iPureIntro.
    simplify_eq /=.
    by apply to_hist_prefix_mono.
  Qed.
  Next Obligation.
    iIntros (E k h Hsub) "#Hinv Hkey".
    unfold OwnMemKey_def, GlobalInv_def, 
      ownMemUser, Seen_def.
    iDestruct "Hkey" as "[%hw ((Hkey & # Hseen) & %Heq)]".
    iModIntro.
    iSplitL.
    - iExists hw.
      iFrame "∗#".
      by iPureIntro.
    - iExists hw.
      iFrame "#".
      by iPureIntro.
  Qed.
  Next Obligation.
    iIntros (E c c' sa sa' ls ls' Hsub) "#Hinv (Hconn1 & Hconn2)".
    destruct (decide (c = c')) as [<- | Hneq].
    - rewrite /ConnectionState_def /connection_state.
      iDestruct "Hconn1" as "[%state ([%v [%γCst [%γA [%γS [%γlk [%γCache [%γMsnap [%γU 
        (%Heq & Hut & Hcli_conn & _)]]]]]]]] & _)]".
      iDestruct "Hconn2" as "[%state' ([%v' [%γCst' [%γA' [%γS' [%γlk' [%γCache' [%γMsnap' [%γU' 
        (%Heq' & Hut' & Hcli_conn' & _)]]]]]]]] & _)]".
      assert (sa = sa') as <-.
      { set_solver. }
      iDestruct (client_connected_agree with "[$Hcli_conn][$Hcli_conn']") as "%Heq_big'".
      simplify_eq.
      by iDestruct (own_valid_2 with "Hut Hut'") as %Hfalse.
    - destruct (decide (sa = sa')) as [<- | Hneq'].
      + rewrite /ConnectionState_def /connection_state.
        iDestruct "Hconn1" as "[%state ([%v [%γCst [%γA [%γS [%γlk [%γCache [%γMsnap [%γU 
          (%Heq & Hut & Hcli_conn & _)]]]]]]]] & _)]".
        iDestruct "Hconn2" as "[%state' ([%v' [%γCst' [%γA' [%γS' [%γlk' [%γCache' [%γMsnap' [%γU' 
          (%Heq' & Hut' & Hcli_conn' & _)]]]]]]]] & _)]".
        iDestruct (client_connected_agree with "[$Hcli_conn][$Hcli_conn']") as "%Heq_big'".
        simplify_eq.
        by iDestruct (own_valid_2 with "Hut Hut'") as %Hfalse.
      + iModIntro.
        by iFrame.
  Qed.

End SI_Resources_intantiation.
