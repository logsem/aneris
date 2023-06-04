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
     Require Import user_params resources.


(** Specifications for read and write operations.  *)
Section Specification.
  Context `{!anerisG Mdl Σ, !User_params, !SI_resources Mdl Σ}.

  Definition write_spec : Prop :=
    ∀ (rpc : val) (sa : socket_address)
      (h : THst) (m : gmap Key val) E
      (k : Key) (v : SerializableVal),
    ⌜k ∈ KVS_keys⌝ -∗
    {{{ TState rpc h m }}}
      write rpc #k v @[ip_of_address sa] E
    {{{ RET #(); TState rpc h (<[k:=v.(SV_val)]> m) }}}.

  Definition read_spec : Prop :=
    ∀ (rpc : val) (sa : socket_address)
    (h : THst) (m : gmap Key val) E
     (k : Key), ⌜k ∈ KVS_keys⌝ -∗
    {{{ TState rpc h m }}}
      read rpc #k @[ip_of_address sa] E
    {{{ (vo : val), RET vo; TState rpc h m ∗
        ⌜k ∉ dom m ∧ vo = $(get_current_state h !! k) ∨
         ∃ v, Some v = (m !! k) ∧ vo = $(Some v)⌝ }}}.

  Definition start_spec : Prop :=
    ∀ (rpc : val) (sa : socket_address) (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (hl hg: THst),
        LHist rpc sa hl ∗ GHist hg ∗ CanStart sa rpc >>>
      start rpc #() @[ip_of_address sa] E
    <<<▷ RET #();
        LHist rpc sa hl ∗ GHist hg ∗ TState rpc hg ∅ >>>.

  Definition commit_spec : Prop :=
   ∀ (rpc : val) (sa : socket_address) (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (hl hs hg: THst) (m : gmap Key val),
    LHist rpc sa hl ∗ TState rpc hs m ∗ GHist hg >>>
      commit rpc #() @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
          CanStart sa rpc ∗
          (⌜b = true⌝ ∗ ⌜can_commit hs m hg = True⌝ ∗
            GHist ((sa, m) :: hg) ∗ LHist rpc sa ((sa, m) :: hl)) ∨
          (⌜b = false⌝ ∗ GHist hg ∗ LHist rpc sa hl) >>>.

(** TODO: Read only transaction *)

(** Fixme *)
(* I think that this spec is wrong! Because h in pre and post of atomic triple
   should not be the same. *)
Definition run_spec : Prop :=
    ∀ (rpc : val) (tbody : val)
      (sa : socket_address) (E : coPset)
      (m : gmap Key val) (h: THst)
      (P : THst → iProp Σ)
      (Q : THst → gmap Key val → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    {{{ TState rpc h ∅ ∗ P h }}}
      tbody rpc #() @[ip_of_address sa] E
    {{{ RET #(); TState rpc h m ∗ Q h m }}} →
    <<< ∀∀ h0, ⌜h0 = h⌝ ∗ (* FIXME: here only for parsing, remove it *)
        CanStart sa rpc ∗ GHist h ∗ LHist rpc sa h ∗ P h >>>
           run rpc tbody #() @[ip_of_address sa] E
    <<<▷∃∃ b,  RET #b;
        CanStart sa rpc ∗
        (⌜b = true⌝ ∗ GHist ((sa, m) :: h) ∗ LHist rpc sa ((sa, m) :: h)) ∨
        (⌜b = false⌝ ∗ GHist h ∗ LHist rpc sa h) >>>.

  Definition init_client_proxy_spec : Prop :=
    ∀ (sa : socket_address),
    {{{ unallocated {[sa]} ∗
        KVS_address ⤇ KVS_si ∗
        sa ⤳ (∅, ∅) ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} }}}
      init_client (s_serializer KVS_serialization)
                  #sa #KVS_address @[ip_of_address sa]
    {{{ rpc, RET rpc; CanStart sa rpc }}}.

Definition init_kvs_spec : Prop :=
  {{{ KVS_address ⤇ KVS_si ∗
        KVS_address ⤳ (∅,∅) ∗
        free_ports (ip_of_address KVS_address)
                   {[port_of_address KVS_address]} }}}
      init_kvs (s_serializer KVS_serialization)
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
  Context `{!anerisG Mdl Σ}.
  Context (CanStart : socket_address → val → iProp Σ).

  Class SI_init `{!User_params} := {
     SI_init_module E :
        True ⊢ |={E}=> ∃ (SIRes : SI_resources Mdl Σ),
       GlobalInv ∗
       GHist [] ∗
       ⌜init_kvs_spec⌝ ∗
       ⌜init_client_proxy_spec⌝ ∗
       ⌜read_spec⌝ ∗
       ⌜write_spec⌝ ∗
       ⌜start_spec⌝ ∗
       ⌜commit_spec⌝ ∗
       ⌜run_spec⌝ }.

End SI_Module.
