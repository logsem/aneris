From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.prelude
     Require Import ser_inj.
From aneris.examples.reliable_communication.lib.repdb
     Require Import model.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events resources.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import
     ras log_resources resources_def
     resources_global_inv resources_local_inv.

Section DB_resources_instance.
  Context `{!anerisG Mdl Σ, !IDBG Σ}.
  Context (γL γM : gname) (N : gmap socket_address gname).

  Global Instance DbRes `{DBP : !DB_params} : DB_resources :=
    {|
      GlobalInv := Global_Inv γL γM N;
      OwnMemKey := own_mem_user γM;
      Obs := own_obs γL;
      OwnMemKey_timeless := OwnMemKey_timeless_holds γM;
      OwnMemKey_exclusive := OwnMemKey_exclusive_holds γM;
      OwnMemKey_fractional := OwnMemKey_fractional_holds γM;
      OwnMemKey_as_fractional := OwnMemKey_as_fractional_holds γM;
      OwnMemKey_combine := OwnMemKey_combine_holds γM;
      OwnMemKey_split := OwnMemKey_split_holds γM;
      OwnMemKey_key :=  OwnMemKey_key_holds γL γM N;
      Obs_timeless := Obs_timeless_holds γL;
      Obs_persistent := Obs_persistent_holds γL;
      Obs_compare := Obs_compare_holds γL;
      Obs_exists_at_leader := Obs_exists_at_leader_holds γL γM N;
      Obs_get_smaller := Obs_get_smaller_holds γL;
      (* Obs_snoc_time := Obs_snoc_time_holds γL γM N; *)
      (* Obs_ext_we := Obs_ext_we_holds γL γM N; *)
      (* Obs_ext_hist := Obs_ext_hist_holds γL γM N; *)
      OwnMemKey_some_obs_we := OwnMemKey_some_obs_we_holds γL γM N;
      OwnMemKey_obs_frame_prefix := OwnMemKey_obs_frame_prefix_holds γL γM N;
      OwnMemKey_obs_frame_prefix_some := OwnMemKey_obs_frame_prefix_some_holds γL γM N;
      OwnMemKey_some_obs_frame := OwnMemKey_some_obs_frame_holds γL γM N;
      OwnMemKey_none_obs := OwnMemKey_none_obs_holds γL γM N;
      (* OwnMemKey_allocated := OwnMemKey_allocated_holds γL γM N; *)
    |}.

End DB_resources_instance.
