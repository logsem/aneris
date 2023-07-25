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
     Require Import user_params.
From aneris.examples.snapshot_isolation.specs.specs_deprecated
     Require Import resources_simpl.


(** Specifications for read and write operations.  *)
Section Specification.
  Context `{!anerisG Mdl Σ, !User_params, !KVS_snapshot_isolation_api,
            !SI_resources Mdl Σ}.

  Definition write_spec : Prop :=
    ∀ (cstate : val) (sa : socket_address)
      (ms : gmap Key (option val))
      (mc : gmap Key val) E
      (k : Key) (v : SerializableVal),
    ⌜k ∈ KVS_keys⌝ -∗
    {{{ ConnectionState cstate (Active ms mc) }}}
      SI_write cstate #k v @[ip_of_address sa] E
    {{{ RET #();
        ConnectionState cstate (Active ms (<[k:= v.(SV_val)]> mc)) }}}.

  Definition read_spec : Prop :=
    ∀ (cstate : val) (sa : socket_address)
      (ms : gmap Key (option val))
      (mc : gmap Key val)
      (vo : option val) E
     (k : Key), ⌜ms !! k = Some vo⌝ -∗
    {{{ ConnectionState cstate (Active ms mc) }}}
      SI_read cstate #k @[ip_of_address sa] E
    {{{ wo, RET $wo; ConnectionState cstate (Active ms mc) ∗
        ⌜(k ∉ dom mc ∧
        match vo with
           | (Some v) => wo = SOMEV v
           | None => wo = NONEV
         end) ∨
        ∃ v, Some v = (mc !! k) ∧ wo = $(Some v)⌝ }}}.

  Definition start_spec : Prop :=
    ∀ (cstate : val) (sa : socket_address)
       (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m : gmap Key (option val)),
       ConnectionState cstate CanStart ∗
       [∗ map] k ↦ vo ∈ m, k ↦ₖ vo >>>
      SI_start cstate @[ip_of_address sa] E
    <<<▷ RET #();
       ConnectionState cstate (Active m ∅) ∗
       [∗ map] k ↦ vo ∈ m, k ↦ₖ vo >>>.

  Definition commit_spec : Prop :=
   ∀ (cstate : val) (sa : socket_address)
    (P :  gmap Key (option val) → iProp Σ)
    (Q :  gmap Key (option val) → gmap Key val → iProp Σ)
    (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m ms: gmap Key (option val)) (mc : gmap Key val),
        ConnectionState cstate (Active ms mc) ∗ P ms ∗
        [∗ map] k ↦ vo ∈ m, k ↦ₖ vo >>>
      SI_commit cstate @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
        ConnectionState cstate CanStart ∗
        (** Transaction has been commited. *)
        (⌜b = true⌝ ∗
           (** Pointers that have been only read *)
           ([∗ set] k ∈ (dom m) ∖ (dom mc),
              let weo :=
              match (m !! k) with
                | None => None
                | Some weo => weo
              end in k ↦ₖ weo) ∗
            (** Pointers that have been written to *)
            ([∗ map] k↦v ∈ mc, k ↦ₖ Some v) ∗ Q ms mc) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗ [∗ map] k ↦ vo ∈ m, k ↦ₖ vo) >>>.

Definition run_spec : Prop :=
    ∀ (cstate : val) (tbody : val)
      (sa : socket_address) (E : coPset)
      (ms : gmap Key (option val)) (mc : gmap Key val)
      (P :  gmap Key (option val) → iProp Σ)
      (Q :  gmap Key (option val) → gmap Key val → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝
    -∗
    {{{ ConnectionState cstate (Active ms ∅) ∗ P ms }}}
      tbody cstate #() @[ip_of_address sa] E
    {{{ RET #(); ConnectionState cstate (Active ms mc) ∗ Q ms mc}}}
    →
    <<< ∀∀ m,
        ConnectionState cstate CanStart ∗ P ms ∗
          [∗ map] k ↦ vo ∈ m, k ↦ₖ vo >>>
           SI_run cstate tbody @[ip_of_address sa] E
    <<<▷∃∃ b,  RET #b;
        ConnectionState cstate CanStart ∗
        (** Transaction has been commited. *)
        (⌜b = true⌝ ∗
           (** Pointers that have been only read *)
           ([∗ set] k ∈ (dom m) ∖ (dom mc),
              let weo :=
              match (m !! k) with
                | None => None
                | Some weo => weo
              end in k ↦ₖ weo) ∗
            (** Pointers that have been written to *)
            ([∗ map] k↦v ∈ mc, k ↦ₖ Some v) ∗ Q ms mc) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗ [∗ map] k ↦ vo ∈ m, k ↦ₖ vo) >>>.


 Definition read_only_commit_spec : Prop :=
   ∀ (cstate : val) (sa : socket_address)
    (P :  gmap Key (option val) → iProp Σ)
    (Q :  gmap Key (option val) → iProp Σ)
    (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m ms: gmap Key (option val)),
        ConnectionState cstate (Active ms ∅) ∗ P ms ∗
        [∗ map] k ↦ vo ∈ m, k ↦ₖ vo >>>
      SI_commit cstate @[ip_of_address sa] E
    <<<▷∃∃ b, RET b; ⌜b = #true⌝ ∗
        ConnectionState cstate CanStart ∗ Q ms ∗
        [∗ map] k ↦ vo ∈ m, k ↦ₖ vo >>>.

  Definition run_read_only_spec : Prop :=
    ∀ (cstate : val) (tbody : val)
      (sa : socket_address) (E : coPset)
      (ms : gmap Key (option val)) (mc : gmap Key val)
      (P :  gmap Key (option val) → iProp Σ)
      (Q :  gmap Key (option val) → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝
    -∗
    {{{ ConnectionState cstate (Active ms ∅) ∗ P ms }}}
      tbody cstate #() @[ip_of_address sa] E
    {{{ RET #(); ConnectionState cstate (Active ms ∅) ∗ Q ms}}}
    →
    <<< ∀∀ m,
        ConnectionState cstate CanStart ∗ P ms ∗
          [∗ map] k ↦ vo ∈ m, k ↦ₖ vo >>>
           SI_run cstate tbody @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
        ConnectionState cstate CanStart ∗
        (** Transaction has been commited. *)
        (⌜b = true⌝ ∗ ([∗ map] k↦vo ∈ m, k ↦ₖ vo) ∗ Q ms) >>>.

  Definition init_client_proxy_spec : Prop :=
    ∀ (sa : socket_address),
    {{{ unallocated {[sa]} ∗
        KVS_address ⤇ KVS_si ∗
        sa ⤳ (∅, ∅) ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} }}}
      SI_init_client_proxy (s_serializer KVS_serialization)
                  #sa #KVS_address @[ip_of_address sa]
    {{{ cstate, RET cstate; ConnectionState cstate CanStart }}}.

Definition init_kvs_spec : Prop :=
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
       ⌜init_kvs_spec⌝ ∗
       ⌜init_client_proxy_spec⌝ ∗
       ⌜read_spec⌝ ∗
       ⌜write_spec⌝ ∗
       ⌜start_spec⌝ ∗
       ⌜commit_spec⌝ ∗
       ⌜run_spec⌝ }.

End SI_Module.

(* TODO: REMOVE THIS LATER, it's just an example of usage. *)
Section Prove_of_t_body_of_some_example.
  Context `{!anerisG Mdl Σ}.
  Context `{!User_params, !KVS_time, !KVS_snapshot_isolation_api, !SI_resources Mdl Σ}.
  Context (rd_spec : read_spec).

  Definition code_snippet : val :=
    λ: "cstate" "k", SI_read "cstate" "k".

  Lemma code_snippet_proof sa (cstate : val) ms m (k : Key) :
     {{{ ⌜k ∈ dom ms⌝ ∗
           ConnectionState cstate (Active ms (<[k:=#42]> m))}}}
       code_snippet cstate #k @[ip_of_address sa]
     {{{ vo, RET vo; ⌜vo = $(Some 42)⌝ }}}.
 Proof.
   rewrite /code_snippet.
   iIntros (Φ) "(%Hkey & HConnectionState) HΦ".
   wp_pures.
   iApply (rd_spec with "[][$HConnectionState]").
   - iPureIntro. admit.
   - iNext.
   iIntros (vo) "(_ & [%Habs | %Hpost])"; iApply "HΦ".
   -- admit.
   -- destruct Hpost as (v & Hv & Hvo).
      by simplify_map_eq /=.
 Admitted.

End Prove_of_t_body_of_some_example.
