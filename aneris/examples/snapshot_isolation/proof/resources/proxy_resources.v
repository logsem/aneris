From iris.algebra Require Import agree auth excl gmap frac_auth updates local_updates.
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


Canonical Structure ip_addressO := leibnizO ip_address.
Canonical Structure proxy_stateO := leibnizO proxy_state.

Record client_gnames : Type  :=
  {
    CGStart  : gname;
    CGActive : gname;
    CGCache  : gname;
    CGLock   : gname;
  }.

Canonical Structure client_gnamesO := leibnizO client_gnames.


Section Proxy.
  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ, !MTS_resources,
              !inG Σ (exclR unitO),
              !inG Σ (agreeR ((ip_addressO * gnameO * gnameO * gnameO * gnameO) : Type)),
              !inG Σ (authR (gmapUR ip_address (agreeR gnameO)))
}.
  Context (γGsnap γT γSrvGnames : gname).

 Definition kvs_valid_snapshot (M : gmap Key (list write_event)) (t : Time) :=
   kvs_valid M t ∧
   ∀ k h, M !! k = Some h → ∀ e, e ∈ h → e.(we_time) < t.

  Definition CanStartToken (γS : gname) : iProp Σ := own γS (Excl ()).
  Definition isActiveToken (γA : gname) : iProp Σ := own γA (Excl ()).

  Definition is_coherent_cache
    (cache_physM : gmap Key val)
    (cacheM : gmap Key (option (val * bool)))
    (Msnap :  gmap Key (list write_event)) :=
               True.

  Definition connection_state_def
    (n : ip_address) (cst : val) (l : loc) (s : proxy_state) (sv : val)
    (γS γA γCache : gname) : iProp Σ :=
      l ↦[n] sv ∗
      MTSCanRequest n cst ∗
      ((⌜sv = NONEV⌝ ∗
        ⌜s = PSCanStart⌝ ∗
        ghost_map_auth γCache 1 ∅ ∗
        CanStartToken γS) ∨
       (∃ (ts : nat) (Msnap : gmap Key (list write_event))
          (cache_physV : val) (cache_physM : gmap Key val)
          (cacheM : gmap Key (option (val * bool))),
           ⌜sv = SOMEV (#ts, cache_physV)⌝ ∗
           ⌜s = PSActive Msnap⌝ ∗
           ⌜is_map cache_physV cache_physM⌝ ∗
           ⌜kvs_valid_snapshot Msnap ts⌝ ∗
           ⌜is_coherent_cache cache_physM cacheM Msnap⌝ ∗
           ownTimeSnap γT ts ∗
           ([∗ map] k ↦ h ∈ Msnap, ownMemSeen γGsnap k h) ∗
           ghost_map_auth γCache 1 cacheM ∗
           isActiveToken γA)).

  Definition connection_state_gen
   (n : ip_address) (c : val) (s : proxy_state) (γlk γS γA γCache : gname)
    : iProp Σ :=
    ∃ (lk : val) (cst : val) (l : loc) (sv : val),
      ⌜c = (lk, (cst, #l))%V⌝ ∗
      is_lock (KVS_InvName .@ "lk") n γlk lk
              (connection_state_def n cst l s sv γS γA γCache).

  Lemma connection_state_gen_persistent n c s γlk γS γA γCache :
    Persistent (connection_state_gen n c s γlk γS γA γCache).
  Proof. apply _. Qed.

  Definition connection_state (n : ip_address) c s : iProp Σ :=
    ∃ (γCst γlk γS γA γCache : gnameO),
      own γSrvGnames (◯ {[n := to_agree γCst]}) ∗
      own γCst (to_agree (n, γlk, γS, γA, γCache)) ∗
      connection_state_gen n c s γlk γS γA γCache ∗
        match s with
        | PSCanStart => isActiveToken γA
        | PSActive _ => CanStartToken γS
        end.

  Definition ownCacheUser
     (c : val) (k : Key) (vo : option val) : iProp Σ :=
    ∃ (n : ip_address) (γCst γlk γS γA γCache : gname) (s : proxy_state)
       (vbo : option (val * bool)),
      own γSrvGnames (◯ {[n := to_agree γCst]}) ∗
      own γCst (to_agree (n, γlk, γS, γA, γCache)) ∗
      connection_state_gen n c s γlk γS γA γCache ∗
      ghost_map_elem γCache k (DfracOwn (1/2)%Qp) vbo ∗
        ⌜match vbo with
         | None => vo = None
         | Some (v, b) => vo = Some v
         end⌝.

  (* Definition key_upd_status (c : val) (k : Key) (b: bool) : iProp Σ := *)
  (*   ∃ n s vbo, *)
  (*     own γCst (n,c) ∗ *)
  (*     connection_state_gen n c s ∗ *)
  (*     ghost_map_elem γCache k (DfracOwn (1/2)%Qp) vbo ∗ *)
  (*     ⌜b = true⌝ → ∃ (v : val), ⌜vbo = Some (v, b)⌝. *)


(*  Definition key_upd_status (c : val) (k : Key) (b : Bool) : iProp Σ := *)
(*    ∃ v. ownCacheUser 1/2 {[ k := v]} ∗ *)

(* OwnLocalKey : Key → val → option val → iProp Σ *)
(*   where "k ↦{ c } vo" := (OwnLocalKey k c vo); *)
(*   OwnLocalKey_timeless k v c:> Timeless (k ↦{c} v); *)

End Proxy.
