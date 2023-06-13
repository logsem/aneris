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
     Require Import user_params time events resources.

Definition can_commit_set `{!KVS_time}
 (m ms : gmap Key (option write_event)) (s : gset Key) : Prop :=
  ∀ (k : Key), k ∈ s → m !! k = ms !! k.

Definition can_commit `{!KVS_time}
 (m ms : gmap Key (option write_event)) (mc : gmap Key (option val * bool)) : Prop :=
  ∀ (k : Key) (v: val), mc !! k = Some (Some v, true) → m !! k = ms !! k.

Definition max_timestamp `{!KVS_time} t (m : gmap Key (option write_event)) : Prop :=
    ∀ k (e : write_event), m !! k = Some (Some e) → TM_lt e.(we_time) t.

Definition weo_val `{!KVS_time} (weo : option write_event) :=
    match weo with
      | None => None
      | Some we => Some we.(we_val)
    end.

Definition commit_event `{!KVS_time}
  (k : Key) (t : Time) (p : option val * bool) (eo : option write_event) :=
    match p with
    | (Some v, true) => Some {|we_key:=k; we_val:=v; we_time:=t|}
    | _              => eo
    end.

(** Specifications for read and write operations.  *)
Section Specification.
  Context `{!anerisG Mdl Σ, !User_params, !KVS_time,
            !KVS_snapshot_isolation_api, !SI_resources Mdl Σ}.

  Definition write_spec : iProp Σ :=
    ∀ (c : val) (sa : socket_address)
      (vo : option val)
      (k : Key) (v : SerializableVal) (b : bool) E,
    ⌜k ∈ KVS_keys⌝ -∗
    {{{ k ↦{c} vo ∗ KeyUpdStatus c k b}}}
      SI_write c #k v @[ip_of_address sa] E
    {{{ RET #(); k ↦{c} Some v.(SV_val) ∗ KeyUpdStatus c k true }}}.

  Definition read_spec : iProp Σ :=
    ∀ (c : val) (sa : socket_address)
      (k : Key) (vo : option val) E,
    ⌜k ∈ KVS_keys⌝ -∗
    {{{ k ↦{c} vo }}}
      SI_read c #k @[ip_of_address sa] E
    {{{ RET $vo; k ↦{c} vo }}}.

   Definition start_spec : iProp Σ :=
    ∀ (c : val) (sa : socket_address)
       (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m : gmap Key (option write_event)),
       ConnectionState c CanStart ∗
       [∗ map] k ↦ eo ∈ m, k ↦ₖ eo >>>
      SI_start c @[ip_of_address sa] E
    <<<▷ RET #();
       ConnectionState c (Active m) ∗
       ([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ∗
       ([∗ map] k ↦ eo ∈ m, k ↦{c} (weo_val eo) ∗ KeyUpdStatus c k false)>>>.



  Definition commit_spec : iProp Σ :=
   ∀ (c : val) (sa : socket_address)
     (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m ms: gmap Key (option write_event))
           (mc : gmap Key (option val * bool)),
        ConnectionState c (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1  ∗ KeyUpdStatus c k p.2) >>>
      SI_commit c @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
        ConnectionState c CanStart ∗
        (** Transaction has been commited. *)
        (⌜b = true⌝ ∗ ⌜can_commit m ms mc⌝ ∗
         ∃ (t: Time), ⌜max_timestamp t m⌝ ∗
          ([∗ map] k↦ eo;p ∈ m; mc, k ↦ₖ commit_event k t p eo)) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗ ⌜¬ can_commit m ms mc⌝ ∗
           [∗ map] k ↦ eo ∈ m, k ↦ₖ eo) >>>.

Definition run_spec : iProp Σ :=
    ∀ (c : val) (tbody : val)
      (sa : socket_address) (E : coPset)
      (P :  gmap Key (option write_event) → iProp Σ)
      (Q :  gmap Key (option write_event) → gmap Key (option val * bool) → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
      (∀ (m0 : gmap Key (option write_event)) (mc : gmap Key (option val * bool)),
         {{{ ([∗ map] k ↦ eo ∈ m0, k ↦{c} (weo_val eo) ∗ KeyUpdStatus c k false) ∗ P m0 }}}
           tbody c #() @[ip_of_address sa] E
         {{{ RET #(); ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1 ∗ KeyUpdStatus c k p.2) ∗ Q m0 mc }}})
    →
    <<< ∀∀ m0, ConnectionState c CanStart ∗
               P m0 ∗
               [∗ map] k ↦ eo ∈ m0, k ↦ₖ eo >>>
           SI_run c tbody @[ip_of_address sa] E
    <<<▷∃∃ m1 mc b, RET #b;
               ConnectionState c CanStart ∗
               (** Transaction has been commited. *)
               (⌜b = true⌝ ∗ ⌜can_commit m1 m0 mc⌝ ∗ Q m0 mc ∗
                ∃ (t: Time), ⌜max_timestamp t m1⌝ ∗
                   ([∗ map] k↦ eo;p ∈ m1; mc, k ↦ₖ commit_event k t p eo)) ∨
               (** Transaction has been aborted. *)
               (⌜b = false⌝ ∗ ⌜¬ can_commit m1 m0 mc⌝ ∗
                [∗ map] k ↦ eo ∈ m1, k ↦ₖ eo) >>>.

 Definition commit_spec_alt : iProp Σ :=
   ∀ (c : val) (sa : socket_address)
     (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m ms: gmap Key (option write_event))
           (mcr : gmap Key (option val))
           (mcw : gmap Key val),
        ConnectionState c (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mcr ∪ dom mcw⌝ ∗ ⌜dom mcr ## dom mcw⌝ ∗
        ([∗ map] k ↦ eo ∈ m, k ↦ₖ eo) ∗
        ([∗ map] k ↦ vo ∈ mcr, k ↦{c}  vo    ∗ KeyUpdStatus c k false) ∗
        ([∗ map] k ↦ v  ∈ mcw, k ↦{c} Some v ∗ KeyUpdStatus c k true) >>>
      SI_commit c @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
        ConnectionState c CanStart ∗
        (** Transaction has been commited. *)
        (⌜b = true⌝ ∗ ⌜can_commit_set m ms (dom mcw)⌝ ∗
         ∃ (t: Time), ⌜max_timestamp t m⌝ ∗
          ([∗ map] k↦_ ∈ mcr, ∃ eo, ⌜m !! k = Some eo⌝ ∗ k ↦ₖ eo) ∗
          ([∗ map] k↦v ∈ mcw, k ↦ₖ Some {|we_key:=k; we_val:=v; we_time:=t|})) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗ ⌜¬ can_commit_set m ms (dom mcw)⌝ ∗
           [∗ map] k ↦ eo ∈ m, k ↦ₖ eo) >>>.

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
