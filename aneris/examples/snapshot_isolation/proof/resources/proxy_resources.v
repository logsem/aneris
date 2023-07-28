From iris.algebra Require Import agree auth excl gmap frac_auth updates local_updates csum.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import lang resources resources inject.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import list_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.lib.mt_server Require Import user_params.
From aneris.examples.snapshot_isolation.specs Require Import user_params.
From aneris.examples.snapshot_isolation.proof
     Require Import time events model.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import resource_algebras server_resources.

Import gen_heap_light.

Inductive proxy_state : Type :=
| PSCanStart
| PSActive of (gmap Key (list write_event)).

Definition hist_to_we (h : list write_event) := last h.


Definition socket_address_to_str (sa : socket_address) : string :=
    match sa with SocketAddressInet ip p => ip +:+ (string_of_pos p) end.

Section Proxy.
  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ, !MTS_resources}.
  (** Those are ghost names allocated before resources are instantiated. *)
  Context (γGsnap γT : gname).
  Context (γKnownClients : gname).

  Definition client_gnames_token_defined γCst γ1 γ2 γ3 γ4 : iProp Σ
    := own γCst (Cinr (to_agree (γ1, γ2, γ3, γ4))).

  Definition client_gnames_token_pending γCst : iProp Σ
    := own γCst (Cinl (Excl ())).

  Definition kvs_valid_snapshot (M : gmap Key (list write_event)) (t : Time) :=
   kvs_valid M t ∧
   ∀ k h, M !! k = Some h → ∀ e, e ∈ h → e.(we_time) < t.

  Definition CanStartToken (γS : gname) : iProp Σ := own γS (Excl ()).
  Definition isActiveToken (γA : gname) : iProp Σ := own γA (Excl ()).

  Definition is_coherent_cache
    (cache_updatesM : gmap Key val)
    (cache_logicalM : gmap Key (option val * bool))
    (Msnap :  gmap Key (list write_event)) :=
      (** Cache Logical and Snapshot Coherence *)
      dom cache_logicalM = dom Msnap ∧
      (∀ k (v : val),
        k ∈ dom cache_logicalM →
        (cache_logicalM !! k) = Some (Some v, false) →
        ∃ h e,
          Msnap !! k = Some h ∧
          hist_to_we h = Some e ∧
          e.(we_val) = v) ∧
      (∀ k (v : val),
         k ∈ dom cache_logicalM →
         (cache_logicalM !! k) = Some (None, false) →
           Msnap !! k = Some []) ∧
      (** Cache Logical and Cache Updates Coherence *)
      dom cache_updatesM ⊆ dom cache_logicalM ∧
      (∀ k (v : val),
        k ∈ dom cache_updatesM →
        cache_updatesM !! k = Some v ↔
                                   cache_logicalM !! k = Some (Some v, true)) ∧
        (∀ k (vo : option val),
           k ∈ dom cache_logicalM →
           (cache_updatesM !! k) = None ↔
                                        cache_logicalM !! k = Some (vo, false)).

  Lemma is_coherent_cache_upd k v cuM cM Msnap :
    is_Some (cM !! k) →
    is_coherent_cache cuM cM Msnap →
    is_coherent_cache (<[k:=v]> cuM) (<[k:=(Some v, true)]> cM) Msnap.
  Proof.
  Admitted.

  Definition is_connected_def
             (n : ip_address) (cst : val) (l : loc) (s : proxy_state) (sv : val)
    (γS γA γCache : gname) : iProp Σ :=
      l ↦[n] sv ∗
      MTSCanRequest n cst ∗
      (
        (** If no active transaction is running on the connection: *)
        (⌜sv = NONEV⌝ ∗
         ⌜s = PSCanStart⌝ ∗
         (** then the lock has start token and guards an empty logical cache map. *)
         ghost_map_auth γCache 1 ∅ ∗
         CanStartToken γS) ∨
        (** Or an active transaction is running: *)
        (∃ (ts : nat) (Msnap : gmap Key (list write_event))
           (cache_updatesL : loc)
           (cache_updatesV : val)
           (cache_updatesM : gmap Key val)
           (cacheM : gmap Key (option val * bool)),
            ⌜sv = SOMEV (#ts, #cache_updatesL)⌝ ∗
            ⌜s = PSActive Msnap⌝ ∗
            (** then lock has active token and guards a logical cache map
                whose domain is equal to the one of the snapshot. *)
            ⌜is_coherent_cache cache_updatesM cacheM Msnap⌝ ∗
            ⌜kvs_valid_snapshot Msnap ts⌝ ∗
            ⌜is_map cache_updatesV cache_updatesM⌝ ∗
            ownTimeSnap γT ts ∗
            ([∗ map] k ↦ h ∈ Msnap, ownMemSeen γGsnap k h) ∗
            cache_updatesL ↦[n] cache_updatesV ∗
            ghost_map_auth γCache 1 cacheM ∗
            isActiveToken γA)).

  Notation connection_token sa γCst := (connected_client_token γKnownClients sa γCst).

  Definition client_can_connect sa : iProp Σ :=
   ∃ γCst, connection_token sa γCst ∗ client_gnames_token_pending γCst.

  Definition client_connected sa γCst γCache γlk γA γS : iProp Σ :=
   connection_token sa γCst ∗ client_gnames_token_defined γCst γCache γlk γA γS.

  Definition is_connected (c : val) (sa : socket_address)
    : iProp Σ :=
    ∃ (lk : val) (cst : val) (l : loc) (sv : val)
      (s : proxy_state)
      (γCst γlk γS γA γCache : gname),
      ⌜c = (#sa, (lk, (cst, #l)))%V⌝ ∗
      client_connected sa γCst γA γS γlk γCache ∗
      is_lock (KVS_InvName .@ (socket_address_to_str sa)) (ip_of_address sa) γlk lk
              (is_connected_def (ip_of_address sa) cst l s sv γS γA γCache).

  Lemma connection_state_gen_persistent c sa : Persistent (is_connected c sa).
  Proof. apply _. Qed.

  (** Tokens forbid the connection state to be duplicable and so
      prohibit concurrent use of start/commit operations which would
      make the use of the library inconsistent because one should not
      run start and commit in parallel, only reads and/or writes. *)
 Definition connection_state (c : val) (sa : socket_address) (s : proxy_state) : iProp Σ :=
   ∃ (sa : socket_address) (v : val) (γCst γA γS γlk γCache : gnameO),
     ⌜c = (#sa, v)%V⌝ ∗
     client_connected sa γCst γA γS γlk γCache ∗
     is_connected c sa ∗
       match s with
       | PSCanStart => isActiveToken γA
       | PSActive _ => CanStartToken γS
       end.


 (** Having a cache pointer guarantees that the connection state is in active
  mode because the domain of the cache map cannot be empty by agreement on
  ghost map. *)
  Definition ownCacheUser (k : Key) (c : val) (vo : option val) : iProp Σ :=
    ∃ (sa : socket_address) (v: val)
      (γCst γA γS γlk γCache : gname) (b : bool),
      ⌜c = (#sa, v)%V⌝ ∗
      client_connected sa γCst γA γS γlk γCache ∗
      ghost_map_elem γCache k (DfracOwn (1/2)%Qp) (vo, b) ∗
        ⌜match vo with
         | None => b = false
         | Some w => KVS_Serializable w
         end⌝.

  Lemma ownCacheUser_timeless k c vo : Timeless (ownCacheUser k c vo).
  Proof. apply _. Qed.

 (** To update cache pointers, one need to change the update status of the key.
  This is enforced by giving half of the pointer permission to the cache pointer
  the other half to the key_upd_status predicate. *)
  Definition key_upd_status (c : val) (k : Key) (b : bool) : iProp Σ :=
    ∃ (sa : socket_address) (vp : val) (γCst γA γS γlk γCache : gname)
      (vo : option val),
      ⌜c = (#sa, vp)%V⌝ ∗
      client_connected sa γCst γA γS γlk γCache ∗
      ghost_map_elem γCache k (DfracOwn (1/2)%Qp) (vo, b) ∗
      (⌜b = true → is_Some vo⌝).


  Lemma own_cache_user_serializable k cst v :
     ownCacheUser k cst (Some v) -∗
     ownCacheUser k cst (Some v) ∗ ⌜KVS_Serializable v⌝.
  Proof.
  Admitted.

  Lemma client_connected_agree sa :
  ∀ γCst γA γS γlk γCache γCst' γA' γS' γlk' γCache',
  client_connected sa γCst γCache γlk γA γS -∗
  client_connected sa γCst' γCache' γlk' γA' γS'  -∗
  ⌜(γCst, γA, γS, γlk, γCache) = (γCst', γA', γS', γlk', γCache')⌝.
  Proof.
  Admitted.

End Proxy.
