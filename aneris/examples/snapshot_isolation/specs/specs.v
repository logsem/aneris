From iris.algebra Require Import auth gmap excl excl_auth.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params time events resources.


(** Specifications for read and write operations.  *)
Section Specification.
  Context `{!anerisG Mdl Σ, !User_params, !KVS_time,
            !SI_resources Mdl Σ}.

  Definition write_spec : Prop :=
    ∀ (rpc : val) (sa : socket_address)
      (ms : gmap Key (option we))
      (mc : gmap Key val) E
      (k : Key) (v : SerializableVal),
    ⌜k ∈ KVS_keys⌝ -∗
    {{{ ConnectionState rpc (Active ms mc) }}}
      write rpc #k v @[ip_of_address sa] E
    {{{ RET #();
        ConnectionState rpc (Active ms (<[k:= v.(SV_val)]> mc)) }}}.

  Definition read_spec : Prop :=
    ∀ (rpc : val) (sa : socket_address)
      (ms : gmap Key (option we))
      (mc : gmap Key val)
      (weo : option we) E
     (k : Key), ⌜ms !! k = Some weo⌝ -∗
    {{{ ConnectionState rpc (Active ms mc) }}}
      read rpc #k @[ip_of_address sa] E
    {{{ (vo : val), RET vo; ConnectionState rpc (Active ms mc) ∗
        ⌜(k ∉ dom mc ∧
        match weo with
           | (Some we) => vo = SOMEV we.(we_val)
           | None => vo = NONEV
         end) ∨
        ∃ v, Some v = (mc !! k) ∧ vo = $(Some v)⌝ }}}.

  Definition start_spec : Prop :=
    ∀ (rpc : val) (sa : socket_address)
       (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m : gmap Key (option we)),
       ConnectionState rpc CanStart ∗
       [∗ map] k ↦ eo ∈ m, k ↦ₖ eo >>>
      start rpc #() @[ip_of_address sa] E
    <<<▷ RET #();
       ConnectionState rpc (Active m ∅) ∗
       [∗ map] k ↦ eo ∈ m, k ↦ₖ eo >>>.

  Definition can_commit
    (m ms : gmap Key (option we))
    (mc : gmap Key val) : Prop :=
    ∀ k, is_Some (mc !! k) → ms !! k = m !! k.

  Definition max_timestamp t (m : gmap Key (option we)) : Prop :=
    ∀ k (e : we), m !! k = Some (Some e) → TM_lt e.(we_time) t.

  Definition commit_spec : Prop :=
   ∀ (rpc : val) (sa : socket_address) (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (m ms: gmap Key (option we)) (mc : gmap Key val),
        ConnectionState rpc (Active ms mc) ∗
        [∗ map] k ↦ eo ∈ m, k ↦ₖ eo >>>
      commit rpc #() @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
        ConnectionState rpc CanStart ∗
        (** Transaction has been commited. *)
        (⌜b = true⌝ ∗ ⌜can_commit m ms mc⌝ ∗
          ∃ (t: Time),
            (** Pointers that have been only read *)
           ([∗ set] k ∈ (dom m) ∖ (dom mc),
              let weo :=
              match (m !! k) with
                | None => None
                | Some weo => weo
              end in k ↦ₖ weo) ∗
            (** Pointers that have been written to *)
            ([∗ map] k↦v ∈ mc,
               k ↦ₖ Some {| we_key := k; we_val := v; we_time := t |}) ∗
             ⌜max_timestamp t m⌝) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗ ⌜¬ can_commit m ms mc⌝ ∗
           [∗ map] k ↦ eo ∈ m, k ↦ₖ eo) >>>.

(** TODO: Read only transaction *)

(** Fixme *)
(* I think that this spec is wrong! Because h in pre and post of atomic triple
   should not be the same. *)
Definition run_spec : Prop :=
    ∀ (rpc : val) (tbody : val)
      (sa : socket_address) (E : coPset)
      (ms : gmap Key (option we)) (mc : gmap Key val)
      (P :  gmap Key (option we) → iProp Σ)
      (Q :  gmap Key (option we) → gmap Key val → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝
    -∗
    {{{ ConnectionState rpc (Active ms ∅) ∗ P ms }}}
      tbody rpc #() @[ip_of_address sa] E
    {{{ RET #(); ConnectionState rpc (Active ms mc) ∗ Q ms mc}}}
    →
    <<< ∀∀ m,
        ConnectionState rpc CanStart ∗ P ms ∗
          [∗ map] k ↦ eo ∈ m, k ↦ₖ eo >>>
           run rpc tbody #() @[ip_of_address sa] E
    <<<▷∃∃ b,  RET #b;
        ConnectionState rpc CanStart ∗
        (** Transaction has been commited. *)
        (⌜b = true⌝ ∗ ⌜can_commit m ms mc⌝ ∗
          ∃ (t: Time),
            (** Pointers that have been only read *)
           ([∗ set] k ∈ (dom m) ∖ (dom mc),
              let weo :=
              match (m !! k) with
                | None => None
                | Some weo => weo
              end in k ↦ₖ weo) ∗
            (** Pointers that have been written to *)
            ([∗ map] k↦v ∈ mc,
               k ↦ₖ Some {| we_key := k; we_val := v; we_time := t |}) ∗
             ⌜max_timestamp t m⌝ ∗ Q ms mc (* TODO : think about the timestamp *)) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗ ⌜¬ can_commit m ms mc⌝ ∗
           [∗ map] k ↦ eo ∈ m, k ↦ₖ eo) >>>.

  Definition init_client_proxy_spec : Prop :=
    ∀ (sa : socket_address),
    {{{ unallocated {[sa]} ∗
        KVS_address ⤇ KVS_si ∗
        sa ⤳ (∅, ∅) ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} }}}
      init_client_proxy (s_serializer KVS_serialization)
                  #sa #KVS_address @[ip_of_address sa]
    {{{ rpc, RET rpc; ConnectionState rpc CanStart }}}.

Definition init_kvs_spec : Prop :=
  {{{ KVS_address ⤇ KVS_si ∗
        KVS_address ⤳ (∅,∅) ∗
        free_ports (ip_of_address KVS_address)
                   {[port_of_address KVS_address]} }}}
      init_server (s_serializer KVS_serialization)
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

  Class SI_init `{!User_params} := {
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
  Context `{!User_params, !KVS_time, !SI_resources Mdl Σ}.
  Context (rd_spec : read_spec).

  Definition code_snippet : val :=
    λ: "rpc" "k", read "rpc" "k".

  Lemma code_snippet_proof sa (rpc : val) ms m (k : Key) :
     {{{ ⌜k ∈ dom ms⌝ ∗
           ConnectionState rpc (Active ms (<[k:=#42]> m))}}}
       code_snippet rpc #k @[ip_of_address sa]
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
