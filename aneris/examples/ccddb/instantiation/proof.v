(** Proof the causal memory implementation w.r.t. modular specification. *)
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import lang resources.
From aneris.examples.ccddb Require Import ccddb_code.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import list_proof map_proof lock_proof network_util_proof.
From aneris.examples.ccddb.spec Require Import spec.
From aneris.examples.ccddb.model Require Import
     model_lst model_gst model_update_system.
From aneris.examples.ccddb.resources Require Import
     base resources_gmem resources_lhst resources_local_inv resources_global_inv.
From aneris.examples.ccddb.proof Require Import proof_of_network proof_of_init.
From aneris.examples.ccddb.instantiation Require Import time events.


Section proof.
  Context `{!anerisG Mdl Σ, !DB_params, !DBG Σ}.

  Local Instance: internal_DBG Σ :=
    Build_internal_DBG
      Σ
      (@DBG_Global_mem_excl _ _ _ _)
      (@DBG_Global_mem_mono _ _ _ _)
      (@DBG_local_history_mono _ _ _ _)
      (@DBG_local_history_gset _ _ _ _)
      (@DBG_lockG _ _ _ _).

  Program Definition db_resources γGauth γGsnap γGkeep γLs : DB_resources Mdl Σ :=
    {| GlobalInv := Global_Inv γGauth γGsnap γGkeep γLs;
       OwnMemUser := own_mem_user γGauth γGsnap;
       OwnMemSys := own_mem_sys γGauth γGsnap γGkeep;
       OwnMemSnapshot := own_mem_snapshot γGsnap;
       OwnMemUser_Exclusive := own_mem_user_excl γGauth γGsnap;
       OwnMemSnapshot_union := own_mem_snapshot_union γGsnap;
       OwnMem_update := own_mem_update γGauth γGsnap γGkeep;
       OwnMemSnapshot_included :=
         own_mem_snapshot_included γGauth γGsnap γGkeep γLs;
       User_Sys_agree := own_mem_user_sys_agree γGauth γGsnap γGkeep;
       User_Snapshot := own_mem_user_snapshot γGauth γGsnap;
       Sys_Snapshot := own_mem_sys_snapshot γGauth γGsnap γGkeep;
       Snapshot_ext := own_mem_snapshot_ext γGauth γGsnap γGkeep γLs;
       Seen := local_history_seen γLs;
       Observe := Observe_lhst;
       init_token := λ i, local_history_Local_inv γLs i ∅;
       Seen_union := local_history_seen_union γGauth γGsnap γGkeep γLs;
       Seen_ext := local_history_seen_ext γGauth γGsnap γGkeep γLs;
       Seen_strong_ext :=
         local_history_seen_strong_ext γGauth γGsnap γGkeep γLs;
       Seen_provenance :=
         local_history_seen_provenance γGauth γGsnap γGkeep γLs;
       Causality := causality γGauth γGsnap γGkeep γLs;
       DB_socket_proto := socket_proto γGsnap |}.

  Lemma init_setup E :
    True ⊢ |={E}=> ∃ (DBRS : DB_resources Mdl Σ),
    GlobalInv ∗
    ([∗ list] i ↦ _ ∈ DB_addresses, init_token i) ∗
    ([∗ set] k ∈ DB_keys, OwnMemUser k ∅) ∗
    init_spec
    (ccddb_init  DB_serialization.(s_serializer).(s_ser)  DB_serialization.(s_serializer).(s_deser)).
  Proof.
    iIntros (_).
    iMod (alloc_gmem with "[]") as
        (γGauth γGsnap γGkeep) "(HG1 & HG2 & HG3 & HG4 & Hmus)"; first done.
    iMod (alloc_lhst with "[]") as (γLs Hlen) "[HLG Hlhs]"; first done.
    iMod (inv_alloc
            DB_InvName _
            (∃ M Ss,
              ⌜length γLs = length DB_addresses⌝ ∗
              ⌜DB_keys = dom M⌝ ∗
              own γGauth (● (make_global_mem M)) ∗
              own γGsnap (● M) ∗
              own γGkeep (● (make_global_mem M)) ∗
              own γGkeep (◯ (make_global_mem M)) ∗
              ([∗ list] γs; S ∈ γLs; Ss, local_history_Global_inv γs S) ∗
              ⌜DBM_GstValid {| Gst_mem := M; Gst_hst := Ss|}⌝)%I
            with  "[HG1 HG2 HG3 HG4 HLG]") as "#Hinv".
    { iNext; iExists empty_gmem, empty_lhsts; iFrame.
      repeat iSplit; first done.
      - by rewrite /empty_gmem dom_gset_to_gmap.
      - iPureIntro; apply DBM_GstValid_empty. }
    iExists (db_resources γGauth γGsnap γGkeep γLs).
    iFrame; iFrame "#".
    iIntros "!> !#" (i z v Hv Hiz Φ) "!# (Hz & Hrs & Hfp & Htk) HΦ".
    iApply (internal_init_spec_holds
              with "[] [] [] [$Hz $Hrs $Hfp $Htk]");
      [done| done|done|].
    iNext.
    iIntros (rd wr) "#(Hseen & Hrd & Hwr)".
    iApply "HΦ".
    iFrame "Hseen". iFrame "#".
  Qed.

  Global Instance init_function : DB_init_function :=
    {|
      init := ccddb_init
                DB_serialization.(s_serializer).(s_ser)
                DB_serialization.(s_serializer).(s_deser);
      |}.

  Global Program Instance db_init : @DB_init _ _ _ _ _ _ _ init_function :=
    {|
      DB_init_time := db_time;
      DB_init_events := db_events;
      DB_init_setup := init_setup;
    |}.

End proof.
