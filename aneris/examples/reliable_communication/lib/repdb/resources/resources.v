From iris.algebra Require Import agree auth excl gmap dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject.
From aneris.aneris_lang.lib Require Import
     list_proof lock_proof monitor_proof map_proof.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import time.

Import gen_heap_light.
Import lock_proof.

Instance: Inhabited (@we int_time) := populate (Build_we "" #() inhabitant).

Global Program Instance Inject_write_event : Inject we val :=
  {| inject a := $(a.(we_key), a.(we_val), a.(we_time))
  |}.
Next Obligation.
  intros w1 w2 Heq.
  inversion Heq as [[Hk Hv Ht]].
  assert (we_time w1 = we_time w2) as Ht'.
  { by apply (inj (R := eq)) in Ht; [ | apply _]. }
  destruct w1, w2; simpl in *.
  by apply Z_of_nat_inj in Ht; subst.
Qed.

Definition write_event := @we int_time.
Definition write_eventO := leibnizO write_event.
Definition wrlog := list write_eventO.



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



(* -------------------------------------------------------------------------- *)
(** The state validity defines coherence of the log and the memory model. *)

Section ValidStates.
  Context `{!anerisG Mdl Σ, !DB_params}.

  (** Validity. *)
  Definition mem_dom (M : gmap Key (option write_event)) := DB_keys = dom M.

  Definition mem_we_key (M : gmap Key (option write_event)) :=
    ∀ k (we : write_event), k ∈ dom M →
                            M !! k = Some (Some we) → we.(we_key) = k.

  Definition mem_log_coh (L : wrlog) (M : gmap Key (option write_event)) :=
    ∀ k, k ∈ dom M → M !! k = Some (at_key k L).

  Definition allocated_in_mem (L : wrlog) (M : gmap Key (option write_event)) :=
    ∀ l k wel, l ≤ₚ L → at_key k l = Some wel →
               ∃ weL, M !! k = Some (Some weL) ∧ wel ≤ₜ weL.

  Definition log_events (L : wrlog) :=
    ∀ i, 0 <= i → i < List.length L →
         ∃ we, List.nth_error L i = Some we ∧ i = we.(we_time).

  Record valid_state (L : wrlog) (M : gmap Key (option write_event)) : Prop :=
    {
      DB_GSTV_mem_dom : mem_dom M;
      DB_GSTV_mem_we_key : mem_we_key M;
      DB_GSTV_mem_log_coh : mem_log_coh L M;
      DB_GSTV_mem_allocated_in_mem : allocated_in_mem L M;
      DB_GSTV_log_events L : log_events L;
    }.

(* TODO : valid state update lemma. *)

End ValidStates.

Section Resources.
  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (γL γM : gname).

  (* ------------------------------------------------------------------------ *)
  (** Abstract global memory definition and properties. *)

  Definition own_mem_user (k : Key) (q: Qp) (a : option write_event) :=
    lmapsto γM k q a.

  Definition own_mem_sys M := gen_heap_light_ctx γM M.

  (** Properties of points-to connective *)
  Lemma OwnMemKey_timeless_holds k q v : Timeless (own_mem_user k q v).
  Proof. Admitted.
  Lemma OwnMemKey_exclusive_holds k q v v' :
    own_mem_user k 1 v ⊢ own_mem_user k q v' -∗ False.
  Proof. Admitted.

  Lemma OwnMemKey_fractioal_holds k v : Fractional (λ q, own_mem_user k q v).
  Proof. Admitted.

  Lemma OwnMemKey_as_fractioal_holds k q v :
    AsFractional (own_mem_user k q v) (λ q, own_mem_user k q v) q.
  Proof. Admitted.

  Lemma OwnMemKey_combine_holds k q q' v v' :
    own_mem_user k q v ∗ own_mem_user k q' v ⊢
    own_mem_user k (q + q') v ∗ ⌜v = v'⌝.
  Proof. Admitted.

  Lemma OwnMemKey_split_holds k q1 q2 v :
    own_mem_user k (q1 + q2) v ⊢ own_mem_user k q1 v ∗ own_mem_user k q2 v.
  Proof. Admitted.



  (* ------------------------------------------------------------------------ *)
  (** Log resources. *)

  (** ** Owned by global invariant of the system. *)
  Definition own_log_global (γ : gname) (l : wrlog) : iProp Σ :=
    own γ (●ML{ DfracOwn (1/2) } l).

  (** ** Owned by the lock invariant of a replica *)
  Definition own_log_local (γ : gname) (l : wrlog) : iProp Σ :=
    own γ (●ML{ DfracOwn (1/2) } l).

  (** ** Duplicable observation describing the prefix of a log. *)
  Definition own_log_obs (γ : gname) (l : wrlog) : iProp Σ :=
    own γ (◯ML l).



  (* ------------------------------------------------------------------------ *)
  (** Resources about free/known replicated logs. *)

  (** ** Ownership to create a new replicated log. *)
  Definition free_replog_token (sa : socket_address) : iProp Σ :=
    own IDBG_free_replog_set_name (GSet {[sa]}).

  (** ** Ownership for a replicated log known by the system. *)
  Definition known_replog_token (sa : socket_address) (γ : gname) : iProp Σ :=
    own IDBG_known_replog_name (◯ {[ sa := to_agree γ ]}).

  Global Instance  known_replog_token_Persistent sa γ :
    Persistent (known_replog_token sa γ).
  Proof. apply _. Qed.

  (** ** Ownership of all replicated logs known by the system. *)
  Definition known_replog_tokens (N : gmap socket_address gname)  : iProp Σ :=
    own IDBG_free_replog_set_name (GSet (dom N)) ∗
    own IDBG_known_replog_name (● (to_agree <$> N : gmap _ _ )).



  (* ------------------------------------------------------------------------ *)
  (** Principal & replicated log ownership predicates *)

  (** ** Principal log. *)
  Definition own_logL_global L : iProp Σ := own γL (●ML{ DfracOwn (1/2) } L).

  Definition own_logL_local L : iProp Σ := own γL (●ML{ DfracOwn (1/2) } L).

  Definition own_logL_obs L : iProp Σ := own γL (◯ML L).

  (** ** Replicated logs. *)

  Definition own_replog_global γ sa l : iProp Σ :=
    known_replog_token sa γ ∗ own_logL_obs l ∗ own_log_global γ l.

  Definition own_replog_local sa l : iProp Σ :=
    ∃ γ, known_replog_token sa γ ∗ own_logL_obs l ∗ own_log_local γ l.

  (* As local ownership is 1/2, the half of it is 1/4. *)
  Definition own_replog_local_half sa l : iProp Σ :=
    ∃ γ, known_replog_token sa γ ∗ own_logL_obs l ∗ own γ (●ML{#1 / 4} l).

  Definition own_replog_obs sa l : iProp Σ :=
    ∃ γ, known_replog_token sa γ ∗ own_logL_obs l.

  (** ** General Obs predicate : socket_address → wrlog → iProp Σ. *)
  Definition own_obs sa l : iProp Σ :=
    (⌜sa = DB_addr⌝ ∗ own_logL_obs l) ∨ own_replog_obs sa l.

  Lemma Obs_timeless_holds a h : Timeless (own_obs a h).
  Proof. apply _. Qed.

  Lemma Obs_persistent_holds a h : Persistent (own_obs a h).
  Proof. apply _. Qed.



  (* ------------------------------------------------------------------------ *)
  (** Definition of the global invariant. *)
  Definition global_inv_def : iProp Σ :=
    ∃ (L : wrlog)
      (M : gmap Key (option write_event))
      (N: gmap socket_address gname),
      ⌜DB_keys = dom M⌝ ∗
      own_mem_sys M ∗
      own_logL_global L ∗
      known_replog_tokens N ∗
      ([∗ map] sa ↦ γ ∈ N, ∃ l, own_replog_global γ sa l) ∗
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
    own_mem_user k q (Some we) ={E}=∗
    own_mem_user k q (Some we) ∗ ⌜we_key we = k⌝.
  Proof. Admitted.

  Lemma Obs_compare_holds a a' h h' E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢ own_obs a h -∗ own_obs a' h' ={E}=∗
    ⌜h ≤ₚ h'⌝ ∨ ⌜h' ≤ₚ h⌝.
  Proof. Admitted.

  Lemma Obs_exists_at_leader_holds a1 h1 E:
    ↑DB_InvName ⊆ E → Global_Inv ⊢
    own_obs a1 h1 ={E}=∗ ∃ h2, own_obs DB_addr h2 ∗ ⌜h1 ≤ₚ h2⌝.
  Proof. Admitted.

  Lemma Obs_get_smaller_holds a h h' E :
    nclose DB_InvName ⊆ E →
    h ≤ₚ h' →
    own_obs a h' ={E}=∗ own_obs a h.
  Proof. Admitted.

  Lemma Obs_snoc_time_holds a h1 e1 h2 E :
    nclose DB_InvName ⊆ E →
    own_obs a (h1 ++ [e1] ++ h2) ={E}=∗
    ⌜∀ e0, e0 ∈ h1 → e0 <ₜ e1⌝ ∧ ⌜∀ e2, e2 ∈ h2 → e1 <ₜ e2⌝.
  Proof. Admitted.

  Lemma Obs_ext_we_holds a a' h h' E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢ own_obs a h -∗ own_obs a' h' ={E}=∗
    ⌜∀ e e', e ∈ h → e' ∈ h' → e =ₜ e' → e = e'⌝.
  Proof. Admitted.

  Lemma Obs_ext_hist_holds a1 a2 h1 h2 k E :
    nclose DB_InvName ⊆ E →
    at_key k h1 = at_key k h2 →
    Global_Inv ⊢ own_obs a1 h1 -∗ own_obs a2 h2 ={E}=∗
    ⌜hist_at_key k h1 = hist_at_key k h2⌝.
  Proof. Admitted.

  Lemma OwnMemKey_some_obs_we_holds k q we E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
    own_mem_user k q (Some we) ={E}=∗
    own_mem_user k q (Some we) ∗
      ∃ h, own_obs DB_addr h ∗ ⌜at_key k h = Some we⌝.
  Proof. Admitted.

  Lemma OwnMemKey_obs_frame_prefix_holds a k q h h' E :
    nclose DB_InvName ⊆ E →
    h ≤ₚ h' →
    Global_Inv ⊢
    own_mem_user k q (at_key k h) ∗ own_obs a h' ={E}=∗
    own_mem_user k q (at_key k h) ∗ ⌜at_key k h = at_key k h'⌝.
  Proof. Admitted.

  Lemma OwnMemKey_obs_frame_prefix_some_holds a k q h h' we E :
    nclose DB_InvName ⊆ E →
    h ≤ₚ h' →
    at_key k h = Some we →
    Global_Inv ⊢
    own_mem_user k q (Some we) ∗ own_obs a h' ={E}=∗
    own_mem_user k q (Some we) ∗ ⌜at_key k h' = Some we⌝.
  Proof. Admitted.

  Lemma OwnMemKey_some_obs_frame_holds a k q we h hf E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
    own_mem_user k q (Some we) ∗ own_obs a (h ++ [we] ++ hf) ={E}=∗
    own_mem_user k q (Some we) ∗ ⌜at_key k hf = None⌝.
  Proof. Admitted.

  Lemma OwnMemKey_none_obs_holds a k q h E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
      own_mem_user k q None ∗ own_obs a h ={E}=∗
      own_mem_user k q None ∗ ⌜hist_at_key k h = []⌝.
  Proof. Admitted.

  Lemma OwnMemKey_allocated_holds k q h0 h1 we0 E :
    nclose DB_InvName ⊆ E →
    h0 ≤ₚ h1 →
    at_key k h0 = Some we0 →
    Global_Inv ⊢
    own_mem_user k q (at_key k h1) ={E}=∗
    ∃ we1, own_mem_user k q (at_key k h1) ∗
             ⌜at_key k h1 = Some we1⌝ ∗ ⌜we0 ≤ₜ we1⌝.
  Proof. Admitted.



  (* ------------------------------------------------------------------------ *)
  (** Is log (TODO: Move in log_proof file.) *)
  Section Log.

  Definition inject_log `{!Inject A val} (xs : list A) :=
    ($xs, #(List.length xs))%V.

  Global Program Instance Inject_log `{!Inject A val}
    : Inject (list A) val := {| inject := inject_log |}.
  Next Obligation.
    intros ? [] xs ys. inversion 1 as [[Hinj Hinj2]].
    by apply Inject_list in Hinj.
  Qed.

  Context `[!Inject A val].

  Definition is_log (logM : list A) (logV : val) :=
    ∃ (lV : val), logV = (lV, #(List.length logM))%V ∧ is_list logM lV.

  Lemma is_log_inject xs l :
    is_log xs l ↔ l = $xs.
  Proof. Admitted.

  (* Definition is_logLoc (logM : list A) (logL : loc) : iProp Σ := *)
  (*   ∃ (logV : val), logL ↦[ip] logV ∗ ⌜is_log logM logV⌝. *)
  End Log.



  (* ------------------------------------------------------------------------ *)
  (** Leader's principal and secondary local invariants. *)



  Notation ipL := (ip_of_address DB_addr).
  Notation ipF := (ip_of_address DB_addr).

  Definition leader_local_main_inv_def (kvsL logL : loc) : iProp Σ :=
   ∃ (logV kvsV : val)
     (kvsM : gmap Key (option write_event))
     (logM : wrlog),
     ⌜is_map kvsV kvsM⌝ ∗
     ⌜is_log logM logV⌝ ∗
     kvsL ↦[ipL] kvsV ∗
     logL ↦[ipL] logV ∗
     own_logL_local logM.

  Definition leader_local_main_inv
    (mγ : gname) (mV : val) (kvsL logL : loc) :=
    is_monitor (DB_InvName .@ "leader_main") ipL mγ mV
               (leader_local_main_inv_def kvsL logL).

  Definition leader_local_secondary_inv_def (logL : loc) : iProp Σ :=
   ∃ (logV : val) (logM : wrlog),
     ⌜is_log logM logV⌝ ∗
     logL ↦[ipF] logV ∗
     own_replog_local DB_addrF logM.

  Definition leader_local_secondary_main_inv
    (mγ : gname) (mV : val) (kvsL logL : loc) :=
    is_monitor (DB_InvName .@ "leader_secondary") ipF mγ mV
               (leader_local_secondary_inv_def logL).



  (* ------------------------------------------------------------------------ *)
  (** Follower's local invariant. *)

  Definition follower_local_inv_def
    (sa : socket_address) (kvsL logL : loc) : iProp Σ :=
    ∃ (logV kvsV : val)
     (kvsM : gmap Key (option write_event))
     (logM : wrlog),
     ⌜is_map kvsV kvsM⌝ ∗
     ⌜is_log logM logV⌝ ∗
     ⌜valid_state logM kvsM⌝ ∗
     kvsL ↦[ip_of_address sa] kvsV ∗
     logL ↦[ip_of_address sa] logV ∗
     own_replog_local sa logM.

  Definition socket_address_to_str (sa : socket_address) : string :=
    match sa with SocketAddressInet ip p => ip +:+ (string_of_pos p) end.

  Definition follower_local_inv
    (sa : socket_address) (mγ : gname) (mV : val) (kvsL logL : loc) :=
    is_monitor (DB_InvName.@socket_address_to_str sa) (ip_of_address sa) mγ mV
               (follower_local_inv_def sa kvsL logL).

End Resources.
