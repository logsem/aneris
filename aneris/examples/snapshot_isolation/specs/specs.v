From iris.algebra Require Import auth gmap excl excl_auth csum.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.algebra.lib Require Import mono_list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
  Require Import serialization_proof.
From aneris.examples.reliable_communication.spec
     Require Import ras.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code_api.
From aneris.examples.snapshot_isolation.specs
  Require Import
  user_params time events aux_defs resource_algebras resources.

Set Default Proof Using "Type".

(** Specifications for read and write operations.  *)
Section Specification.
  Context `{!anerisG Mdl Σ, !User_params,
            !KVS_snapshot_isolation_api, !SI_resources Mdl Σ}.

  Definition write_spec : Prop :=
    ∀ (c : val) (sa : socket_address)
      (vo : option val)
      (k : Key) (v : SerializableVal) (b : bool) ,
      ⌜k ∈ KVS_keys⌝ -∗
      IsConnected c sa -∗
    {{{ k ↦{c} vo ∗ KeyUpdStatus c k b}}}
      SI_write c #k v @[ip_of_address sa] 
    {{{ RET #(); k ↦{c} Some v.(SV_val) ∗ KeyUpdStatus c k true }}}.

  Definition read_spec : Prop :=
    ∀ (c : val) (sa : socket_address)
      (k : Key) (vo : option val),
    ⌜k ∈ KVS_keys⌝ -∗
    IsConnected c sa -∗
    {{{ k ↦{c} vo }}}
      SI_read c #k @[ip_of_address sa] 
    {{{ RET $vo; k ↦{c} vo }}}.

   Definition start_spec : Prop :=
    ∀ (c : val) (sa : socket_address)
       (E : coPset),
      ⌜↑KVS_InvName ⊆ E⌝ -∗
      IsConnected c sa -∗
    <<< ∀∀ (m : gmap Key Hist),
       ConnectionState c sa CanStart ∗
       [∗ map] k ↦ h ∈ m, k ↦ₖ h >>>
      SI_start c @[ip_of_address sa] E
    <<<▷ RET #();
       ConnectionState c sa (Active m) ∗
       ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
       ([∗ map] k ↦ h ∈ m, k ↦{c} (last h) ∗ KeyUpdStatus c k false) ∗
       ([∗ map] k ↦ h ∈ m, Seen k h)>>>.

  Definition commit_spec : Prop :=
   ∀ (c : val) (sa : socket_address)
     (E : coPset),
     ⌜↑KVS_InvName ⊆ E⌝ -∗
     IsConnected c sa -∗
    <<< ∀∀ (m ms: gmap Key Hist)
           (mc : gmap Key (option val * bool)),
        ConnectionState c sa (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1  ∗ KeyUpdStatus c k p.2) >>>
      SI_commit c @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
        ConnectionState c sa CanStart ∗
        (** Transaction has been commited. *)
        ((⌜b = true⌝ ∗ ⌜can_commit m ms mc⌝ ∗
          ([∗ map] k↦ h;p ∈ m; mc,
            k ↦ₖ commit_event p h ∗ Seen k (commit_event p h))) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗ ⌜¬ can_commit m ms mc⌝ ∗
           [∗ map] k ↦ h ∈ m, k ↦ₖ h ∗ Seen k h)) >>>.

(* Definition run_spec : iProp Σ :=
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
               ((⌜b = true⌝ ∗ ⌜can_commit m1 m0 mc⌝ ∗ Q m0 mc ∗
                ∃ (t: Time), ⌜max_timestamp t m1⌝ ∗
                   ([∗ map] k↦ eo;p ∈ m1; mc, k ↦ₖ commit_event k t p eo)) ∨
               (** Transaction has been aborted. *)
               (⌜b = false⌝ ∗ ⌜¬ can_commit m1 m0 mc⌝ ∗
                [∗ map] k ↦ eo ∈ m1, k ↦ₖ eo)) >>>. *)

  Definition init_client_proxy_spec : Prop :=
    ∀ (sa : socket_address),
    {{{ unallocated {[sa]} ∗
        KVS_address ⤇ KVS_si ∗
        sa ⤳ (∅, ∅) ∗
        KVS_ClientCanConnect sa ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} }}}
      SI_init_client_proxy (s_serializer KVS_serialization)
                  #sa #KVS_address @[ip_of_address sa]
    {{{ cstate, RET cstate; ConnectionState cstate sa CanStart ∗
                            IsConnected cstate sa }}}.

Definition init_kvs_spec : Prop :=
  {{{ KVS_address ⤇ KVS_si ∗
        KVS_address ⤳ (∅,∅) ∗
        free_ports (ip_of_address KVS_address)
                   {[port_of_address KVS_address]} ∗
      KVS_Init }}}
      SI_init_server (s_serializer KVS_serialization)
        #KVS_address
        @[(ip_of_address KVS_address)]
    {{{ RET #(); True }}}.

End Specification.

Canonical Structure valO := leibnizO val.

Notation KVSG Σ := (IDBG Σ).
 
Definition KVSΣ : gFunctors :=
  #[
      ghost_mapΣ Key (list write_eventO);
      ghost_mapΣ Key (option val * bool);
      GFunctor (authR (gmapUR Key (max_prefix_listR
                                     write_eventO)));
      GFunctor ((authR (gen_heapUR Key val)));
      GFunctor (authR (gmapUR nat (agreeR (gmapUR Key (max_prefix_listR write_eventO)))));
      GFunctor
        (authR (gmapUR socket_address (agreeR (leibnizO gname))));
      GFunctor ((csumR
                   (exclR unitR)
                   (agreeR ((gnameO * gnameO * gnameO * gnameO * gnameO) : Type))));
     GFunctor (exclR unitO);
     GFunctor (authUR (gsetUR nat));
     mono_natΣ;
     ras.SpecChanΣ;
     lockΣ].

Instance subG_KVSΣ {Σ} : subG KVSΣ Σ → KVSG Σ.
Proof. econstructor; solve_inG. Qed.

Section SI_Module.
  Context `{!anerisG Mdl Σ, !User_params,
            !KVSG Σ, !KVS_snapshot_isolation_api}.

  Class SI_client_toolbox `{!SI_resources Mdl Σ} := {
    SI_init_kvs_spec : init_kvs_spec ;
    SI_init_client_proxy_spec : init_client_proxy_spec;
    SI_read_spec : read_spec ;
    SI_write_spec : write_spec;
    SI_start_spec : start_spec;
    SI_commit_spec : commit_spec;
  }.
 
   Class SI_init := {
    SI_init_module E (clients : gset socket_address) :
      ↑KVS_InvName ⊆ E →
       ⊢ |={E}=>
      ∃ (res : SI_resources Mdl Σ),
        ([∗ set] k ∈ KVS_keys, k ↦ₖ []) ∗
        KVS_Init ∗
        GlobalInv ∗
        ([∗ set] sa ∈ clients, KVS_ClientCanConnect sa) ∗
        ⌜init_kvs_spec⌝ ∗
        ⌜init_client_proxy_spec⌝ ∗
        ⌜read_spec⌝ ∗
        ⌜write_spec⌝ ∗
        ⌜start_spec⌝ ∗
        ⌜commit_spec⌝
     }.
   
End SI_Module.
 
