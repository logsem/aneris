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
     Require Import user_params resources.

Definition can_commit `{User_params}
 (m ms : gmap Key Hist) (mc : gmap Key (option val * bool)) : bool :=
  bool_decide (∀ (k : Key), k ∈ KVS_keys →
  match (mc !! k : option (option val * bool)) with
    | Some (vo, true) => bool_decide (m !! k = ms !! k) 
    | _ => true                       
  end).

Definition commit_event
  (p : option val * bool) (h : Hist) :=
    match p with
    | (Some v, true) => v :: h
    | _              => h
    end.

Definition hist_val (h : Hist) :=
  match h with 
  | v :: t => Some v
  | [] => None
  end.

(** Specifications for read and write operations.  *)
Section Specification.
  Context `{!anerisG Mdl Σ, !User_params,
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
    <<< ∀∀ (m : gmap Key Hist),
       ConnectionState c CanStart ∗
       [∗ map] k ↦ h ∈ m, k ↦ₖ h >>>
      SI_start c @[ip_of_address sa] E
    <<<▷ RET #();
       ConnectionState c (Active m) ∗
       ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
       ([∗ map] k ↦ h ∈ m, k ↦{c} (hist_val h) ∗ KeyUpdStatus c k false) ∗
       ([∗ map] k ↦ h ∈ m, Seen k h)>>>.

  Definition commit_spec : iProp Σ :=
   ∀ (c : val) (sa : socket_address)
     (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m ms: gmap Key Hist)
           (mc : gmap Key (option val * bool)),
        ConnectionState c (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1  ∗ KeyUpdStatus c k p.2) >>>
      SI_commit c @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
        ConnectionState c CanStart ∗
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
                   {[port_of_address KVS_address]} ∗
      KVS_Init }}}
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

Instance subG_KVSΣ {Σ} : subG KVSΣ Σ → KVSG Σ.
Proof. econstructor; solve_inG. Qed.

Section SI_Module.
  Context `{!anerisG Mdl Σ, !User_params,
    !KVS_snapshot_isolation_api}.

  Class SI_specs `{!SI_resources Mdl Σ} := {
    SI_init_kvs_spec : ⊢ init_kvs_spec;
    SI_init_client_proxy_spec : ⊢ init_client_proxy_spec;
    SI_read_spec : ⊢ read_spec ;
    SI_write_spec : ⊢ write_spec;
    SI_start_spec : ⊢ start_spec;
    SI_commit_spec : ⊢ commit_spec;
    (* SI_run_Spec : ⊢ run_spec; *)
  }.

  Class SI_init := {
    SI_init_module E :
      True ⊢ |={E}=> ∃ (res : SI_resources Mdl Σ) (specs : SI_specs),
      GlobalInv ∗ ([∗ set] k ∈ KVS_keys, k ↦ₖ [])
  }.

End SI_Module.
