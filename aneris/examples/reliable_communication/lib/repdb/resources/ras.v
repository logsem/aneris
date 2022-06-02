From iris.algebra Require Import auth gmap dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.bi.lib Require Import fractional.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events.
From aneris.examples.reliable_communication.lib.repdb
     Require Import model.

Import gen_heap_light.
Import lock_proof.


(* -------------------------------------------------------------------------- *)
(** Resource Algebras and global ghost names needed to define resources. *)

Class IDBG Σ :=
  { IDBG_Global_mem :>
      inG Σ (authR (gen_heapUR Key (option write_event)));
    IDBG_Global_history_mono :>
      inG Σ (mono_listUR write_eventO);
    IDBG_Known_replog :>
      inG Σ (authR (gmapUR socket_address (agreeR gnameO)));
    IDBG_free_replogG :>
      inG Σ (gset_disjUR socket_address);
    IDBG_lockG :> lockG Σ;
    IDBG_known_replog_name : gname;
    IDBG_free_replog_set_name : gname;
  }.
