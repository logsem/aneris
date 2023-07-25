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
     Require Import user_params resources_hist.


(** Specifications for read and write operations.  *)
Section Specification.
  Context `{!anerisG Mdl Σ, !User_params, !KVS_snapshot_isolation_api, !SI_resources Mdl Σ}.

  Definition write_spec : Prop :=
    ∀ (cstate : val) (sa : socket_address)
      (h : THst) (m : gmap Key val) E
      (k : Key) (v : SerializableVal),
    ⌜k ∈ KVS_keys⌝ -∗
    {{{ TState cstate h m }}}
      SI_write cstate #k v @[ip_of_address sa] E
    {{{ RET #(); TState cstate h (<[k:=v.(SV_val)]> m) }}}.

  Definition read_spec : Prop :=
    ∀ (cstate : val) (sa : socket_address)
    (h : THst) (m : gmap Key val) E
     (k : Key), ⌜k ∈ KVS_keys⌝ -∗
    {{{ TState cstate h m }}}
      SI_read cstate #k @[ip_of_address sa] E
    {{{ (vo : val), RET vo; TState cstate h m ∗
        ⌜k ∉ dom m ∧ vo = $(get_current_state h !! k) ∨
         ∃ v, Some v = (m !! k) ∧ vo = $(Some v)⌝ }}}.

  Definition start_spec : Prop :=
    ∀ (cstate : val) (sa : socket_address) (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (hl hg: THst),
        LHist cstate sa hl ∗ GHist hg ∗ CanStart sa cstate >>>
      SI_start cstate @[ip_of_address sa] E
    <<<▷ RET #();
        LHist cstate sa hl ∗ GHist hg ∗ TState cstate hg ∅ >>>.

  Definition commit_spec : Prop :=
   ∀ (cstate : val) (sa : socket_address)
     (P : THst → iProp Σ)
     (Q : THst → gmap Key val → iProp Σ)
    (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    <<< ∀∀ (hl hs hg: THst) (m : gmap Key val),
    LHist cstate sa hl ∗ GHist hg ∗ TState cstate hs m ∗ P hs >>>
      SI_commit cstate @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
          CanStart sa cstate ∗
          (⌜b = true⌝ ∗ ⌜can_commit hs m hg⌝ ∗
            GHist ((sa, m) :: hg) ∗ LHist cstate sa ((sa, m) :: hl) ∗ Q hs m) ∨
          (⌜b = false⌝ ∗ ⌜¬ can_commit hs m hg⌝ ∗
            GHist hg ∗ LHist cstate sa hl) >>>.

(** TODO: Read only transaction *)

Definition run_spec : Prop :=
    ∀ (cstate : val) (tbody : val)
      (sa : socket_address) (E : coPset)
      (m : gmap Key val) (h: THst) (hl : THst)
      (P : THst → iProp Σ)
      (Q : THst → gmap Key val → iProp Σ),
    ⌜↑KVS_InvName ⊆ E⌝
    -∗
    {{{ TState cstate h ∅ ∗ P h }}}
      tbody cstate #() @[ip_of_address sa] E
    {{{ RET #(); TState cstate h m ∗ Q h m }}}
    →
    <<< ∀∀ (x : unit), CanStart sa cstate ∗ GHist h ∗ LHist cstate sa hl ∗ P h >>>
           SI_run cstate tbody @[ip_of_address sa] E
    <<<▷∃∃ b h',  RET #b;
        ⌜h ≤ₚ h'⌝ ∗
        CanStart sa cstate ∗
        (⌜b = true⌝ ∗ ⌜can_commit h m h'⌝ ∗
                      GHist ((sa, m) :: h') ∗ LHist cstate sa ((sa, m) :: hl) ∗ Q h m) ∨
        (⌜b = false⌝ ∗ ⌜¬ can_commit h m h'⌝ ∗ GHist h' ∗ LHist cstate sa hl) >>>.

  Definition init_client_proxy_spec : Prop :=
    ∀ (sa : socket_address),
    {{{ unallocated {[sa]} ∗
        KVS_address ⤇ KVS_si ∗
        sa ⤳ (∅, ∅) ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} }}}
      SI_init_client_proxy (s_serializer KVS_serialization)
                  #sa #KVS_address @[ip_of_address sa]
    {{{ cstate, RET cstate; CanStart sa cstate }}}.

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
  Context `{!anerisG Mdl Σ}.

  Class SI_init `{!User_params, !KVS_snapshot_isolation_api} := {
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

(* TODO: REMOVE THIS LATER, it's just an example of usage. *)
Section Prove_of_t_body_of_some_example.
  Context `{!anerisG Mdl Σ}.
  Context `{!User_params, !KVS_snapshot_isolation_api, !SI_resources Mdl Σ}.
  Context (rd_spec : read_spec).

  Definition code_snippet : val :=
    λ: "cstate" "k", SI_read "cstate" "k".

  Lemma code_snippet_proof sa (cstate : val) h m (k : Key) :
     {{{ ⌜k ∈ KVS_keys⌝ ∗
           TState cstate h (<[k:=#42]> m)}}}
       code_snippet cstate #k @[ip_of_address sa]
     {{{ vo, RET vo; ⌜vo = $(Some 42)⌝ }}}.
 Proof.
   rewrite /code_snippet.
   iIntros (Φ) "(Hkey & HTState) HΦ".
   wp_pures.
   iApply (rd_spec with "[$][$HTState]").
   iNext.
   iIntros (vo) "(_ & [%Habs | %Hpost])"; iApply "HΦ";
     first by set_solver.
   destruct Hpost as (v & Hv & Hvo).
   by simplify_map_eq /=.
 Qed.

End Prove_of_t_body_of_some_example.
