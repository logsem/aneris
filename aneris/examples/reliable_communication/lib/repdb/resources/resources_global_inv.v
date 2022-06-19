From iris.algebra Require Import agree auth excl gmap dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.lib.repdb
     Require Import model.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params events.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import ras resources_def.

Import gen_heap_light.
Import lock_proof.


Section Global_Invariant.

  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (γL γM : gname).

  (* ------------------------------------------------------------------------ *)
  (** Definition of the global invariant. *)
  Definition global_inv_def : iProp Σ :=
    ∃ (L : wrlog)
      (M : gmap Key (option write_event))
      (N: gmap socket_address gname),
      ⌜DB_keys = dom M⌝ ∗
      ⌜dom N = DB_followers ∪ {[DB_addrF]}⌝ ∗
      ⌜DB_followers ## {[DB_addrF]}⌝ ∗
      own_mem_sys γM M ∗
      own_logL_global γL L ∗
      known_replog_tokens N ∗
      ([∗ map] sa ↦ γ ∈ N, ∃ l, own_replog_global γL γ sa l) ∗
      ⌜valid_state L M⌝.

  Definition Global_Inv := inv DB_InvName global_inv_def.

(* TODO : update lemma ? *)

  (* ------------------------------------------------------------------------ *)
  (** Properties entailed by the global invariant. *)

  Lemma Global_InvPersistent : Persistent Global_Inv.
  Proof. apply _. Qed.

  Lemma OwnMemKey_key_holds k q we E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
    own_mem_user γM k q (Some we) ={E}=∗
    own_mem_user γM k q (Some we) ∗ ⌜we_key we = k⌝.
  Proof. Admitted.

  Lemma Obs_compare_holds a a' h h' E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢ own_obs γL a h -∗ own_obs γL a' h' ={E}=∗
    ⌜h ≤ₚ h'⌝ ∨ ⌜h' ≤ₚ h⌝.
  Proof. Admitted.

  Lemma Obs_exists_at_leader_holds a1 h1 E:
    ↑DB_InvName ⊆ E → Global_Inv ⊢
    own_obs γL a1 h1 ={E}=∗ ∃ h2, own_obs γL DB_addr h2 ∗ ⌜h1 ≤ₚ h2⌝.
  Proof. Admitted.

  Lemma Obs_get_smaller_holds a h h' E :
    nclose DB_InvName ⊆ E →
    h ≤ₚ h' →
    own_obs γL a h' ={E}=∗ own_obs γL a h.
  Proof. Admitted.

  Lemma Obs_snoc_time_holds a h1 e1 h2 E :
    nclose DB_InvName ⊆ E →
    own_obs γL a (h1 ++ [e1] ++ h2) ={E}=∗
    ⌜∀ e0, e0 ∈ h1 → e0 <ₜ e1⌝ ∧ ⌜∀ e2, e2 ∈ h2 → e1 <ₜ e2⌝.
  Proof. Admitted.

  Lemma Obs_ext_we_holds a a' h h' E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢ own_obs γL a h -∗ own_obs γL a' h' ={E}=∗
    ⌜∀ e e', e ∈ h → e' ∈ h' → e =ₜ e' → e = e'⌝.
  Proof. Admitted.

  Lemma Obs_ext_hist_holds a1 a2 h1 h2 k E :
    nclose DB_InvName ⊆ E →
    at_key k h1 = at_key k h2 →
    Global_Inv ⊢ own_obs γL a1 h1 -∗ own_obs γL a2 h2 ={E}=∗
    ⌜hist_at_key k h1 = hist_at_key k h2⌝.
  Proof. Admitted.

 Lemma OwnMemKey_wo_obs_holds k q wo E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
    own_mem_user γM k q wo ={E}=∗
    own_mem_user γM k q wo ∗
      ∃ h, own_obs γL DB_addr h ∗ ⌜at_key k h = wo⌝.
  Proof. Admitted.


  Lemma OwnMemKey_some_obs_we_holds k q we E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
    own_mem_user γM k q (Some we) ={E}=∗
    own_mem_user γM k q (Some we) ∗
      ∃ h, own_obs γL DB_addr h ∗ ⌜at_key k h = Some we⌝.
  Proof. Admitted.

  Lemma OwnMemKey_obs_frame_prefix_holds a k q h h' E :
    nclose DB_InvName ⊆ E →
    h ≤ₚ h' →
    Global_Inv ⊢
    own_mem_user γM k q (at_key k h) ∗ own_obs γL a h' ={E}=∗
    own_mem_user γM k q (at_key k h) ∗ ⌜at_key k h = at_key k h'⌝.
  Proof. Admitted.

  Lemma OwnMemKey_obs_frame_prefix_some_holds a k q h h' we E :
    nclose DB_InvName ⊆ E →
    h ≤ₚ h' →
    at_key k h = Some we →
    Global_Inv ⊢
    own_mem_user γM k q (Some we) ∗ own_obs γL a h' ={E}=∗
    own_mem_user γM k q (Some we) ∗ ⌜at_key k h' = Some we⌝.
  Proof. Admitted.

  Lemma OwnMemKey_some_obs_frame_holds a k q we h hf E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
    own_mem_user γM k q (Some we) ∗ own_obs γL a (h ++ [we] ++ hf) ={E}=∗
    own_mem_user γM k q (Some we) ∗ ⌜at_key k hf = None⌝.
  Proof. Admitted.

  Lemma OwnMemKey_none_obs_holds a k q h E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
      own_mem_user γM k q None ∗ own_obs γL a h ={E}=∗
      own_mem_user γM k q None ∗ ⌜hist_at_key k h = []⌝.
  Proof. Admitted.

  Lemma OwnMemKey_allocated_holds k q h0 h1 we0 E :
    nclose DB_InvName ⊆ E →
    h0 ≤ₚ h1 →
    at_key k h0 = Some we0 →
    Global_Inv ⊢
    own_mem_user γM k q (at_key k h1) ={E}=∗
    ∃ we1, own_mem_user γM k q (at_key k h1) ∗
             ⌜at_key k h1 = Some we1⌝ ∗ ⌜we0 ≤ₜ we1⌝.
  Proof. Admitted.

  Lemma Obs_we_serializable a h E we :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
    own_obs γL a (h ++ [we]) ={E}=∗
    ⌜Serializable
     (prod_serialization
        (prod_serialization string_serialization DB_serialization)
        int_serialization) ($ we)⌝.
  Proof. Admitted.

End Global_Invariant.
