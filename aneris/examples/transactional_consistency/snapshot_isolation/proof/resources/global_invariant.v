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
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  time events.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.proof Require Import model.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.resources Require Import
  server_resources.


Section Global_Invariant.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ, !MTS_resources}.
  Context (clients : gset socket_address).
  Context (γKnownClients : gname).
  Context (γGauth γGsnap γT γTrs : gname).

  (* ------------------------------------------------------------------------ *)
  (** Definition of the global invariant. *)
  Definition global_inv_def : iProp Σ :=
    ∃ (M : global_mem) (S : snapshots) (T : Time)
      (gM : gmap socket_address gname),
      ownMemGlobal γGauth γGsnap M ∗
      ownSnapAuth γTrs S ∗
      ownTimeGlobal γT T ∗
      connected_clients γKnownClients gM ∗
      ⌜dom gM = clients⌝ ∗
      ⌜kvs_valid M S T⌝.

  Definition Global_Inv : iProp Σ :=
    inv KVS_InvName global_inv_def.

  Lemma Global_InvPersistent : Persistent Global_Inv.
  Proof. apply _. Qed.

  Lemma ownMemSeen_valid E k h h' :
    nclose KVS_InvName ⊆ E →
    Global_Inv ⊢
    ownMemSeen γGsnap k h -∗
    ownMemUser γGauth γGsnap k h' ={E}=∗
    ownMemUser γGauth γGsnap k h' ∗ ⌜h `prefix_of` h'⌝.
  Proof.
    iIntros (?) "#Hginv #Hm Hu".
    iDestruct "Hu" as "(Hu & #Hum)".
    rewrite /Global_Inv /ownMemSeen.
    iInv KVS_InvName
      as (M S T gM)
           ">((HmemA & HmemM) & ? & ? & ? & ? & %Hvalid)" "Hcl".
    iDestruct (ownMemSeen_lookup with "HmemM Hm")
      as (h1) "(%Hh1 & %Hh2)".
    iDestruct (ghost_map_lookup with "HmemA Hu") as "%Hh3".
    simplify_eq /=.
    iFrame "#". iFrame.
    iMod ("Hcl" with "[-]") as "_".
    { iNext. do 4 iExists _. by iFrame. }
    iModIntro.
    rewrite Hh2 in Hh3.
    set_solver. 
  Qed.

End Global_Invariant.
