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
From aneris.examples.snapshot_isolation.specs Require Import user_params.
From aneris.examples.snapshot_isolation.proof
     Require Import time events model.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import resource_algebras server_resources proxy_resources.


Section Global_Invariant.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ, !MTS_resources}.
  Context (clients : gset socket_address).
  Context (γKnownClients : gname).
  Context (γGauth γGsnap γT γTss : gname).

  (* ------------------------------------------------------------------------ *)
  (** Definition of the global invariant. *)
  Definition global_inv_def : iProp Σ :=
    ∃ (M : gmap Key (list write_event))
      (T : Time)
      (Tss : gset nat)
      (gM : gmap socket_address gname),
      ownMemGlobal γGauth γGsnap M ∗
      ownTimeGlobal γT T ∗
      ownTimeStartsAuth γTss Tss ∗
      connected_clients γKnownClients gM ∗
      ⌜dom gM = clients⌝ ∗
      ⌜kvs_valid M T Tss⌝.

  Definition Global_Inv : iProp Σ :=
    inv KVS_InvName global_inv_def.

  Lemma Global_InvPersistent : Persistent Global_Inv.
  Proof. apply _. Qed.

  Lemma ownMemSeen_valid E k h h' :
    nclose KVS_InvName ⊆ E →
    Global_Inv ⊢
    ownMemSeen γGsnap k h -∗ ownMemUser γGauth γGsnap k h' ={E}=∗
    ownMemUser γGauth γGsnap k h' ∗ ⌜h `prefix_of` h'⌝.
  Proof.
    iIntros (?) "#Hginv #Hm Hu".
    iDestruct "Hu" as "(Hu & #Hum)".
    rewrite /Global_Inv /ownMemSeen.
    iInv KVS_InvName
      as (M T Tss gM)
           ">((HmemA & HmemM) & ? & ? & ? & ? & %Hvalid)" "Hcl".
    iDestruct (ownMemSeen_lookup with "HmemM Hm")
      as (h1) "(%Hh1 & %Hh2)".
    iDestruct (ghost_map_lookup with "HmemA Hu") as "%Hh3".
    simplify_eq /=.
    iFrame "#". iFrame.
    iMod ("Hcl" with "[-]") as "_".
    { iNext. do 4 iExists _. by iFrame. }
    by iModIntro.
  Qed.


  (* (** NB: not sure we will use this lemma. *) *)
  (* (** FIXME: Maybe don't need the GlobalInv, *)
  (*     in which case update the specs.resources *) *)
  (* Lemma Connection_State_relation E k r ms h : *)
  (*     ↑KVS_InvName ⊆ E -> *)
  (*     Global_Inv ⊢ *)
  (*     connection_state γGsnap γT γKnownClients r (PSActive ms) -∗ *)
  (*     ownMemUser γGauth γGsnap k h ={E}=∗ *)
  (*     connection_state γGsnap γT γKnownClients r (PSActive ms) ∗ *)
  (*     ownMemUser γGauth γGsnap k h ∗ *)
  (*     ⌜k ∈ dom ms → *)
  (*     ∀ h', ms !! k = Some h' → h' `prefix_of` h ⌝. *)
  (* Proof. *)
  (* Admitted.  *)

  (* (** NB: not sure we will use this lemma. *) *)
  (* (** FIXME: Maybe don't need the GlobalInv, *)
  (*     in which case update the specs.resources *) *)
  (* Lemma OwnMemUser_OwnLocalKey_coh k h vo c E : *)
  (*       ↑KVS_InvName ⊆ E -> *)
  (*       h ≠ [] -> *)
  (*       Global_Inv ⊢ *)
  (*       ownMemUser γGauth γGsnap k h -∗ *)
  (*       ownCacheUser γKnownClients k c vo ={E}=∗ *)
  (*       ownMemUser γGauth γGsnap k h ∗ *)
  (*       ownCacheUser γKnownClients k c vo ∗ ⌜is_Some vo⌝. *)
  (* Proof. *)
  (* Admitted. *)

  (* (** NB: not sure we will use this lemma. *) *)
  (* (** FIXME: Maybe don't need the GlobalInv, *)
  (*     in which case update the specs.resources *) *)
  (*   Lemma connection_state_Keys E r ms : *)
  (*     ↑KVS_InvName ⊆ E -> *)
  (*       Global_Inv ⊢ *)
  (*       connection_state γGsnap γT γKnownClients r (PSActive ms) ={E}=∗ *)
  (*       connection_state γGsnap γT γKnownClients r (PSActive ms) ∗ *)
  (*       ⌜dom ms ⊆ KVS_keys⌝. *)
  (*   Proof. *)
  (*   Admitted. *)

End Global_Invariant.
