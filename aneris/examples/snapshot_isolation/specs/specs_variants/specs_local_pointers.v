From iris.algebra Require Import auth gmap excl excl_auth.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code_api.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params time.
From aneris.examples.snapshot_isolation.specs.specs_variants
     Require Import events_local_pointers resources_local_pointers.

Definition cache_commit `{!KVS_time}  c k t : option write_event :=
    match c.(cache_newv) with
      | None => c.(cache_snap)
      | Some v => Some {| we_key := k;  we_val := v; we_time := t; |}
    end.

Definition max_timestamp `{!KVS_time} t (m : gmap Key (option write_event)) : Prop :=
    ∀ k (e : write_event), m !! k = Some (Some e) → TM_lt e.(we_time) t.

Definition can_commit `{!KVS_time}
    (m : gmap Key (option write_event))
    (mc : gmap Key cache_event) : Prop :=
    ∀ (k : Key) (ce : cache_event),
       k ∈ dom m → (mc !! k) = Some ce → is_Some (ce.(cache_newv)) →
       m !! k = Some ce.(cache_snap).

Definition cache_updv `{!KVS_time} (c : cache_event) (v : val) : cache_event :=
  {|cache_snap := c.(cache_snap); cache_newv := Some v |}.

Definition cache_getv `{!KVS_time} (c : cache_event) : option val :=
  match c.(cache_newv) with
  | Some v => Some v
  | None =>
      match c.(cache_snap) with
      | Some we => Some we.(we_val)
      | None => None
      end
  end.

Definition cache_make `{!KVS_time} (we : option write_event) : cache_event :=
  {|cache_snap := we; cache_newv := None |}.

Definition kvs_snap_coh `{!KVS_time}
  (ms m : gmap Key (option write_event)) : Prop :=
  dom m = dom ms ∧
    ∀ k we, k ∈ dom ms →
       ms !! k = Some (Some we) →
      ∃ we', m !! k = Some (Some we') ∧ we ≤ₜ we'.

Definition snap_cache_coh `{!KVS_time}
  (ms : gmap Key (option write_event)) (mc : gmap Key cache_event) : Prop :=
  dom ms = dom mc ∧
    ∀ k (wo : option write_event), k ∈ dom ms →
       ms !! k = Some wo →
      ∃ c, mc !! k = Some c ∧ c.(cache_snap) = wo.


(** Specifications for read and write operations.  *)
Section Specification.
  Context `{!anerisG Mdl Σ, !User_params, !KVS_time,
            !KVS_snapshot_isolation_api, !SI_resources Mdl Σ}.


  Definition write_spec : iProp Σ :=
    ∀ (cstate : val) (sa : socket_address)
      (c : cache_event)
      (k : Key) (v : SerializableVal) E,
    ⌜k ∈ KVS_keys⌝ -∗
    {{{ k ↦ₜ c }}}
      SI_write cstate #k v @[ip_of_address sa] E
    {{{ RET #(); k ↦ₜ cache_updv c v }}}.

  Definition read_spec : iProp Σ :=
    ∀ (cstate : val) (sa : socket_address)
      (k : Key) (c : cache_event) E,
    {{{ k ↦ₜ c }}}
      SI_read cstate #k @[ip_of_address sa] E
    {{{ vo, RET vo; ⌜vo = $(cache_getv c)⌝ ∗ k ↦ₜ c }}}.

  Definition start_spec : iProp Σ :=
    ∀ (cstate : val) (sa : socket_address)
       (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m : gmap Key (option write_event)),
       ConnectionState cstate CanStart ∗
       [∗ map] k ↦ eo ∈ m, k ↦ₖ eo >>>
      SI_start cstate @[ip_of_address sa] E
    <<<▷ RET #();
       ConnectionState cstate (Active m) ∗
       ([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ∗
       ([∗ map] k ↦ eo ∈ m, k ↦ₜ cache_make eo) >>>.

  Definition commit_spec : iProp Σ :=
   ∀ (cstate : val) (sa : socket_address)
     (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m ms: gmap Key (option write_event))
           (mc : gmap Key cache_event),
        ConnectionState cstate (Active ms) ∗
        ⌜snap_cache_coh ms mc⌝ ∗
        ([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ∗
        ([∗ map] k ↦ c ∈ mc, k ↦ₜ c) >>>
      SI_commit cstate @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
        ConnectionState cstate CanStart ∗
         ⌜kvs_snap_coh ms m⌝ ∗
        (** Transaction has been commited. *)
        (⌜b = true⌝ ∗ ⌜can_commit m mc⌝ ∗
          ∃ (t: Time), ⌜max_timestamp t m⌝ ∗
            ([∗ map] k↦c ∈ mc,  k ↦ₖ cache_commit c k t)) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗ ⌜¬ can_commit m mc⌝ ∗
           [∗ map] k ↦ eo ∈ m, k ↦ₖ eo) >>>.

Definition run_spec : iProp Σ :=
    ∀ (cstate : val) (tbody : val)
      (sa : socket_address) (E : coPset)
      (P :  gmap Key (option write_event) → iProp Σ)
      (Q :  gmap Key (option write_event) → gmap Key cache_event → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
      (∀ (m0 : gmap Key (option write_event)),
         {{{ ([∗ map] k ↦ wo ∈ m0, k ↦ₜ cache_make wo) ∗ P m0 }}}
           tbody cstate #() @[ip_of_address sa] E
         {{{ RET #();
             ∃ (mc : gmap Key cache_event),
               ⌜dom m0 = dom mc⌝ ∗ ([∗ map] k ↦ c ∈ mc, k ↦ₜ c) ∗ Q m0 mc }}})
    →
    <<< ∀∀ m0, ConnectionState cstate CanStart ∗
               P m0 ∗
               [∗ map] k ↦ eo ∈ m0, k ↦ₖ eo >>>
           SI_run cstate tbody @[ip_of_address sa] E
    <<<▷∃∃ m1 mc b, RET #b;
               ConnectionState cstate CanStart ∗
               ⌜kvs_snap_coh m0 m1⌝ ∗
               (** Transaction has been commited. *)
               (⌜b = true⌝ ∗ ⌜can_commit m1 mc⌝ ∗
                ∃ (t: Time), ⌜max_timestamp t m1⌝ ∗
                  ([∗ map] k↦c ∈ mc,  k ↦ₖ cache_commit c k t) ∗ Q m0 mc) ∨
               (** Transaction has been aborted. *)
               (⌜b = false⌝ ∗ ⌜¬ can_commit m1 mc⌝ ∗
                [∗ map] k ↦ eo ∈ m1, k ↦ₖ eo) >>>.

  Definition init_client_proxy_spec : iProp Σ :=
    ∀ (sa : socket_address),
    {{{ unallocated {[sa]} ∗
        KVS_address ⤇ KVS_si ∗
        sa ⤳ (∅, ∅) ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} }}}
      SI_init_client_proxy (s_serializer KVS_serialization)
                  #sa #KVS_address @[ip_of_address sa]
    {{{ cstate, RET cstate; ConnectionState cstate CanStart }}}.

Definition init_kvs_spec : iProp Σ :=
  {{{ KVS_address ⤇ KVS_si ∗
        KVS_address ⤳ (∅,∅) ∗
        free_ports (ip_of_address KVS_address)
                   {[port_of_address KVS_address]} }}}
      SI_init_server (s_serializer KVS_serialization)
        #KVS_address
        @[(ip_of_address KVS_address)]
    {{{ RET #(); True }}}.

End Specification.


Class KVSG  Σ :=
  {
    KVS_lockG :> lockG Σ;
    (* TODO ... : ... ; *)
  }.

Definition KVSΣ : gFunctors :=
  #[ (* TODO ... ; *) lockΣ].

Instance subG_DBΣ {Σ} : subG KVSΣ Σ → KVSG Σ.
Proof. econstructor; solve_inG. Qed.

Section SI_Module.
  Context `{!anerisG Mdl Σ, !KVS_time}.

  Class SI_init `{!User_params, !KVS_snapshot_isolation_api} := {
     SI_init_module E :
        True ⊢ |={E}=> ∃ (SIRes : SI_resources Mdl Σ),
       GlobalInv ∗
       ([∗ set] k ∈ KVS_keys, k ↦ₖ None) ∗
       init_kvs_spec ∗
       init_client_proxy_spec ∗
       read_spec ∗
       write_spec ∗
       start_spec ∗
       commit_spec ∗
       run_spec }.

End SI_Module.
