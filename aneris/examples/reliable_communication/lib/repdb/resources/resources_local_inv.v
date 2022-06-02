From iris.algebra Require Import agree auth excl gmap dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof.
From aneris.examples.reliable_communication.lib.repdb
     Require Import model.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params events.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import
     ras resources_def.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import log_proof.

Import gen_heap_light.
Import lock_proof.

Section Local_Invariants.

  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (γL γM : gname).

  (* ------------------------------------------------------------------------ *)
  (** Leader's principal and secondary local invariants. *)


  Definition leader_local_main_inv_def (kvsL logL : loc) : iProp Σ :=
   ∃ (logV kvsV : val)
     (kvsM : gmap Key val)
     (logM : wrlog),
     ⌜is_map kvsV kvsM⌝ ∗
     ⌜is_log logM logV⌝ ∗
     ⌜valid_state_local logM kvsM⌝ ∗
     kvsL ↦[ip_of_address DB_addr] kvsV ∗
     logL ↦[ip_of_address DB_addr] logV ∗
     own_logL_local γL logM.

  Definition leader_local_main_inv
    (mγ : gname) (mV : val) (kvsL logL : loc) :=
    is_monitor (DB_InvName .@ "leader_main") (ip_of_address DB_addr) mγ mV
               (leader_local_main_inv_def kvsL logL).

  Definition leader_local_secondary_inv_def (logL : loc) : iProp Σ :=
   ∃ (logV : val) (logM : wrlog),
     ⌜is_log logM logV⌝ ∗
     logL ↦[ip_of_address DB_addrF] logV ∗
     own_replog_local γL DB_addrF logM.

  Definition leader_local_secondary_main_inv
    (mγ : gname) (mV : val) (kvsL logL : loc) :=
    is_monitor (DB_InvName .@ "leader_secondary") (ip_of_address DB_addrF) mγ mV
               (leader_local_secondary_inv_def logL).

  (* ------------------------------------------------------------------------ *)
  (** Follower's local invariant. *)

  Definition follower_local_inv_def
    (sa : socket_address) (kvsL logL : loc) : iProp Σ :=
    ∃ (logV kvsV : val)
     (kvsM : gmap Key val)
     (logM : wrlog),
     ⌜is_map kvsV kvsM⌝ ∗
     ⌜is_log logM logV⌝ ∗
     ⌜valid_state_local logM kvsM⌝ ∗
     kvsL ↦[ip_of_address sa] kvsV ∗
     logL ↦[ip_of_address sa] logV ∗
     own_replog_local γL sa logM.

  Definition socket_address_to_str (sa : socket_address) : string :=
    match sa with SocketAddressInet ip p => ip +:+ (string_of_pos p) end.

  Definition follower_local_inv
    (sa : socket_address) (mγ : gname) (mV : val) (kvsL logL : loc) :=
    is_monitor (DB_InvName.@socket_address_to_str sa) (ip_of_address sa) mγ mV
               (follower_local_inv_def sa kvsL logL).


End Local_Invariants.
