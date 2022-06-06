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
  Context (γL : gname).

  (* ------------------------------------------------------------------------ *)
  (** Leader's principal and secondary local invariants. *)

  Definition leader_local_main_res (kvsL : loc) (logM : wrlog) : iProp Σ :=
   ∃ (kvsV : val) (kvsM : gmap Key val),
     ⌜is_map kvsV kvsM⌝ ∗
     ⌜valid_state_local logM kvsM⌝ ∗
     kvsL ↦[ip_of_address DB_addr] kvsV.

  Definition leader_local_main_inv
    (kvsL logL : loc) (mγ : gname) (mV : val) : iProp Σ :=
    is_monitor (DB_InvName .@ "leader_main") (ip_of_address DB_addr) mγ mV
               (log_monitor_inv_def
                  (ip_of_address DB_addr) γL (1/2) logL
                  (leader_local_main_res kvsL)).

  Definition leader_local_secondary_res (γF : gname) (logM : wrlog) : iProp Σ :=
    known_replog_token DB_addrF γF ∗ own_logL_obs γL logM.

  Definition leader_local_secondary_inv
    (logFL : loc) (γF : gname) (mγ : gname) (mV : val) : iProp Σ :=
      is_monitor (DB_InvName .@ "leader_secondary") (ip_of_address DB_addrF) mγ mV
                 (log_monitor_inv_def
                    (ip_of_address DB_addrF) γF (1/4) logFL
                    (leader_local_secondary_res γF)).

  (* ------------------------------------------------------------------------ *)
  (** Follower's local invariant. *)

  Definition follower_local_res
    (kvsL : loc) (sa : socket_address) (γsa : gname) (logM : wrlog) : iProp Σ :=
    ∃ (kvsV : val) (kvsM : gmap Key val),
     ⌜is_map kvsV kvsM⌝ ∗
     ⌜valid_state_local logM kvsM⌝ ∗
     kvsL ↦[ip_of_address sa] kvsV ∗
     known_replog_token sa γsa ∗
     own_logL_obs γL logM.

  Definition socket_address_to_str (sa : socket_address) : string :=
    match sa with SocketAddressInet ip p => ip +:+ (string_of_pos p) end.

  Definition follower_local_main_inv (kvsL logL : loc)
    (sa : socket_address) (γsa : gname) (mγ : gname) (mV : val)  : iProp Σ :=
     is_monitor (DB_InvName.@socket_address_to_str sa) (ip_of_address sa) mγ mV
               (log_monitor_inv_def
                  (ip_of_address sa) γsa (1/2) logL
                  (follower_local_res kvsL sa γsa)).

End Local_Invariants.
