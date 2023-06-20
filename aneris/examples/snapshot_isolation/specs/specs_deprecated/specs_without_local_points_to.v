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
     Require Import time events resources_without_local_points_to.


(** Specifications for read and write operations.  *)
Section Specification.
  Context `{!anerisG Mdl Σ, !User_params, !KVS_time,
            !KVS_snapshot_isolation_api, !SI_resources Mdl Σ}.

  Definition write_spec : Prop :=
    ∀ (cstate : val) (sa : socket_address)
      (ms : gmap Key (option write_event))
      (mc : gmap Key val) E
      (k : Key) (v : SerializableVal),
    ⌜k ∈ KVS_keys⌝ -∗
    {{{ ConnectionState cstate (Active ms mc) }}}
      SI_write cstate #k v @[ip_of_address sa] E
    {{{ RET #();
        ConnectionState cstate (Active ms (<[k:= v.(SV_val)]> mc)) }}}.

  Definition read_spec : Prop :=
    ∀ (cstate : val) (sa : socket_address)
      (ms : gmap Key (option write_event))
      (mc : gmap Key val)
      (eo : option write_event) E
     (k : Key), ⌜ms !! k = Some eo⌝ -∗
    {{{ ConnectionState cstate (Active ms mc) }}}
      SI_read cstate #k @[ip_of_address sa] E
    {{{ (ro : val), RET $ro; ConnectionState cstate (Active ms mc) ∗
        ⌜(k ∉ dom mc ∧
        match eo with
           | (Some we) => ro = SOMEV we.(we_val)
           | None => ro = NONEV
         end) ∨
        ∃ v, Some v = (mc !! k) ∧ ro = $(Some v)⌝ }}}.

  Definition start_spec : Prop :=
    ∀ (cstate : val) (sa : socket_address)
       (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m : gmap Key (option write_event)),
       ConnectionState cstate CanStart ∗
       [∗ map] k ↦ eo ∈ m, k ↦ₖ eo >>>
      SI_start cstate @[ip_of_address sa] E
    <<<▷ RET #();
       ConnectionState cstate (Active m ∅) ∗
       [∗ map] k ↦ eo ∈ m, k ↦ₖ eo >>>.

  Definition can_commit
    (m ms : gmap Key (option write_event))
    (mc : gmap Key val) : Prop :=
    ∀ k, is_Some (mc !! k) → ms !! k = m !! k.

  Definition max_timestamp t (m : gmap Key (option write_event)) : Prop :=
    ∀ k (e : write_event), m !! k = Some (Some e) → TM_lt e.(we_time) t.

  Definition commit_spec : Prop :=
   ∀ (cstate : val) (sa : socket_address)
     (P :  gmap Key (option write_event) → iProp Σ)
     (Q :  gmap Key (option write_event) → gmap Key val → iProp Σ)
     (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m ms: gmap Key (option write_event)) (mc : gmap Key val),
        ConnectionState cstate (Active ms mc) ∗
        [∗ map] k ↦ eo ∈ m, k ↦ₖ eo ∗ P ms >>>
      SI_commit cstate @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
        ConnectionState cstate CanStart ∗
        (** Transaction has been commited. *)
        (⌜b = true⌝ ∗ ⌜can_commit m ms mc⌝ ∗
          ∃ (t: Time),
            (** Pointers that have been only read *)
           ([∗ set] k ∈ (dom m) ∖ (dom mc),
              let write_evento :=
              match (m !! k) with
                | None => None
                | Some write_evento => write_evento
              end in k ↦ₖ write_evento) ∗
            (** Pointers that have been written to *)
            ([∗ map] k↦v ∈ mc,
               k ↦ₖ Some {| we_key := k; we_val := v; we_time := t |}) ∗
             ⌜max_timestamp t m⌝ ∗ Q ms mc) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗ ⌜¬ can_commit m ms mc⌝ ∗
           [∗ map] k ↦ eo ∈ m, k ↦ₖ eo) >>>.

Definition run_spec : Prop :=
    ∀ (cstate : val) (tbody : val)
      (sa : socket_address) (E : coPset)
      (P :  gmap Key (option write_event) → iProp Σ)
      (Q :  gmap Key (option write_event) → gmap Key val → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝
    -∗
      (∀ ms mc,
    {{{ ConnectionState cstate (Active ms ∅) ∗ P ms }}}
      tbody cstate #() @[ip_of_address sa] E
    {{{ RET #(); ConnectionState cstate (Active ms mc) ∗ Q ms mc }}})
    →
    <<< ∀∀ m0,
        ConnectionState cstate CanStart ∗ P m0 ∗
          [∗ map] k ↦ eo ∈ m0, k ↦ₖ eo >>>
           SI_run cstate tbody @[ip_of_address sa] E
    <<<▷∃∃ m1 mc b,  RET #b;
        (** TODO : coh(m0,m1) = m0 *)
        ConnectionState cstate CanStart ∗
        (** Transaction has been commited. *)
        (⌜b = true⌝ ∗ ⌜can_commit m1 m0 mc⌝ ∗
          ∃ (t: Time),
            (** Pointers that have been only read *)
           ([∗ set] k ∈ (dom m1) ∖ (dom mc),
              let write_evento :=
              match (m0 !! k) with
                | None => None
                | Some write_evento => write_evento
              end in k ↦ₖ write_evento) ∗
            (** Pointers that have been written to *)
            ([∗ map] k↦v ∈ mc,
               k ↦ₖ Some {| we_key := k; we_val := v; we_time := t |}) ∗
             ⌜max_timestamp t m1⌝ ∗ Q m0 mc) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗ ⌜¬ can_commit m1 m0 mc⌝ ∗
           [∗ map] k ↦ eo ∈ m1, k ↦ₖ eo) >>>.

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
