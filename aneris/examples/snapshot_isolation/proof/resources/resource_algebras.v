From iris.algebra Require Import auth gmap dfrac.
From iris.algebra.lib Require Import mono_list .
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.bi.lib Require Import fractional.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params.
From aneris.examples.snapshot_isolation.proof
     Require Import time events.
From aneris.examples.snapshot_isolation.proof
     Require Import model.
Import gen_heap_light.
Import lock_proof.


(* -------------------------------------------------------------------------- *)
(** Some of Resource Algebras and global ghost names needed to define resources. *)

Class IDBG Σ :=
  {
    (** Key-Value store *)
    IDBG_Global_mem :> ghost_mapG Σ Key (list write_event);
    IDBG_Global_mem' :> inG Σ (authR (gmapUR Key (max_prefix_listR write_eventO)));
    (** Time *)
    IDBG_TimeStamp :> mono_natG Σ;
    (** Lock *)
    IDBG_lockG :> lockG Σ;
  }.
