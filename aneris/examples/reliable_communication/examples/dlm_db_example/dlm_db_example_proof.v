From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang Require Import tactics proofmode.
From aneris.aneris_lang.program_logic
     Require Import aneris_weakestpre aneris_lifting.
From aneris.aneris_lang.lib Require Import assert_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.prelude
     Require Import ser_inj.
From aneris.examples.reliable_communication.lib.dlm
     Require Import dlm_code.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code.
From aneris.examples.reliable_communication.lib.dlm
     Require Import dlm_prelude dlm_code dlm_spec.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import
     ras resources api_spec.
From aneris.examples.reliable_communication.examples.dlm_db_example
     Require Import dlm_db_example_code.

(* -------------------------------------------------------------------------- *)
(** The definition of the user parameters for DB and DL. *)
(* -------------------------------------------------------------------------- *)
Definition DBSrv (sa saF : socket_address) : DB_params :=
  {| DB_addr := sa;
    DB_addrF := saF;
    DB_keys := {["x"; "y"]};
    DB_InvName := (nroot .@ "DBInv");
    DB_serialization := int_serialization;
    DB_ser_inj := int_ser_is_ser_injective;
    DB_ser_inj_alt := int_ser_is_ser_injective_alt |}.


Definition DLSrv (sa : socket_address) : DL_params :=
  {| DL_server_addr := sa;
    DL_namespace := (nroot .@ "DLInv"); |}.

(* -------------------------------------------------------------------------- *)
(** The definition of the resource guarded by the distributed lock manager. *)
(* -------------------------------------------------------------------------- *)
Section Shared_resource_def.
  Context `{!anerisG Mdl Σ}.
  Context `{!DB_time, !DBG Σ}.
  Context (DBP: DB_params).
  Context `{!@DB_resources _ _ _ _ DBP}.

  Definition SharedRes : iProp Σ :=
    ∃ (xv yv : option we) (h : ghst),
      "x" ↦ₖ xv ∗
      "y" ↦ₖ yv ∗
      Obs DB_addr h ∗
      ⌜at_key "x" h = xv⌝ ∗
      ⌜at_key "y" h = yv⌝ ∗
      ⌜∀ xw yw,
         (xv = Some xw ∧ xw.(we_val) = #37) ↔
         (yv = Some yw ∧ yw.(we_val) = #1)⌝.

End Shared_resource_def.



(* -------------------------------------------------------------------------- *)
(** The proof of the internal do_writes call *)
(* -------------------------------------------------------------------------- *)
Section proof_of_the_do_writes.
  (* NotaBene : Leader-Followers resources must be introduced before the
     distributed lock resources, because the shared resource definition above
     involves abstract memory pointers.  *)
  Context `{!anerisG Mdl Σ, !lockG Σ}.
  Context (sa sFa : socket_address).
  Notation DBP := (DBSrv sa sFa).
  (* Leader-Followers top-level resources. *)
  Context `{TM: !DB_time, !DBG Σ}.
  (* Context `{DBP: !DB_params}. *)
  Context `{!@DB_resources _ _ _ _ DBP }.
  Notation DLRes := (SharedRes DBP).
  (* Leader-Followers allocated resources (per call of `do_writes`) *)
  Context (wr : val) (clt_01 : socket_address).
  Context (HWriteSpec : ⊢ ∀ k v h, simplified_write_spec wr clt_01 k v h).

  (* Distributed Lock top-level resources. *)
  Context `{!DlockG Σ, !DL_resources}.
  (* Distributed Lock allocated resources (per call of `do_writes`) *)
  Context (dl : val) (clt_00 : socket_address).
  Context (HAcqSpec : dl_acquire_spec DLRes clt_00 dl).
  Context (HRelSpec : dl_release_spec DLRes clt_00 dl).
  Context (HipEq : ip_of_address clt_00 = ip_of_address clt_01).

  Lemma wp_do_writes :
    {{{ DLockCanAcquire clt_00 dl DLRes }}}
      do_writes dl wr @[ip_of_address clt_00]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Hacq HΦ".
    rewrite /do_writes.
    wp_pures.
    wp_apply (HAcqSpec with "[$Hacq]").
    iIntros (v) "(-> & Hrel & Hdlk & Hres)".
    wp_pures.
    iDestruct "Hres" as (xv yv h) "(Hx & Hy & #Hobs & %Hhx & %Hhy & Hcnd)".
    rewrite HipEq.
    wp_apply (HWriteSpec $! "x" (SerVal #37) h _ with "[Hx Hobs]").
    { iExists _. iFrame "#∗". done. }
    iIntros "Hpost".
  Admitted.

End proof_of_the_do_writes.

(* -------------------------------------------------------------------------- *)
(** The proof of the internal do_reads call *)
(* -------------------------------------------------------------------------- *)
Section proof_of_the_do_reads.
  (* NotaBene : Leader-Followers resources must be introduced before the
     distributed lock resources, because the shared resource definition above
     involves abstract memory pointers.  *)
  Context `{!anerisG Mdl Σ, !lockG Σ}.
  Context (sa sFa : socket_address).
  Notation DBP := (DBSrv sa sFa).
  (* Leader-Followers top-level resources. *)
  Context `{TM: !DB_time, !DBG Σ}.
  (* Context `{DBP: !DB_params}. *)
  Context `{!@DB_resources _ _ _ _ DBP }.
  Notation DLRes := (SharedRes DBP).
  (* Leader-Followers allocated resources (per call of `do_reads`) *)
  Context (rd : val) (clt_11 : socket_address).
  Context (HReadSpec : ⊢ ∀ k q h, @read_spec _ _ _ _ DBP _ rd clt_11 k q h).
   (* Distributed Lock top-level resources. *)
  Context `{!DlockG Σ, !DL_resources}.
  (* Distributed Lock allocated resources (per call of `do_writes`) *)
  Context (dl : val) (clt_10 : socket_address).
  Context (HAcqSpec : dl_acquire_spec DLRes clt_10 dl).
  Context (HRelSpec : dl_release_spec DLRes clt_10 dl).
  Context (HipEq : ip_of_address clt_10 = ip_of_address clt_11).

  (* NotaBene : the spec of dl_wait_on_read can be applied to
     generic key `k` and value `v` (instead of x and 37) only if
     a resource k ↦ₖ{q} v is either provided in the precondition
     or if it is also guarded by the distributed lock. *)
  Lemma wp_dl_wait_on_read :
    {{{ DLockCanAcquire clt_10 dl DLRes }}}
      dl_wait_on_read dl rd #"x" #37 @[ip_of_address clt_10]
    {{{ RET #(); True }}}.
  Proof.
  Admitted.

  Lemma wp_do_reads :
    {{{ DLockCanAcquire clt_10 dl DLRes }}}
      do_reads dl rd @[ip_of_address clt_10]
    {{{ RET #(); True }}}.
  Proof.
  Admitted.

End proof_of_the_do_reads.


(* -------------------------------------------------------------------------- *)
(** The proof of the node 0 (writer) *)
(* -------------------------------------------------------------------------- *)
Section proof_of_the_node_0.
  Context `{!anerisG Mdl Σ, !lockG Σ}.
  Context (dba dbFa dlma : socket_address).
  Notation DBP := (DBSrv dba dbFa).
  (* Leader-Followers top-level resources. *)
  Context `{TM: !DB_time, !DBG Σ}.
  (* Context `{DBP: !DB_params}. *)
  Context `{!@DB_resources _ _ _ _ DBP }.
  Notation DLRes := (SharedRes DBP).
  (* Distributed Lock top-level resources. *)
  Context `{!DlockG Σ}.
  Context (DBL := (DLSrv dlma)).
  Context `{!DL_resources}.
  Context (leader_si : message → iProp Σ).
  Context (HstartProxySpec :
            ⊢ (∀ A ca, @init_client_proxy_leader_spec _ _ _ _ DBP _ A ca leader_si)).
  Context (HsubscribeClient :
            ⊢ (∀ sa (A : gset socket_address),
                 @dl_subscribe_client_spec _ _ _ DBL _ DLRes sa A)).

  Lemma proof_of_node0 (clt_00 clt_01 : socket_address) (A : gset socket_address) :
    ip_of_address clt_00 = ip_of_address clt_01 →
    {{{
        (* preconditions for subscribing client to dlock. *)
        ⌜clt_00 ∉ A⌝ ∗
        fixed A ∗
        free_ports (ip_of_address clt_00) {[port_of_address clt_00]} ∗
        clt_00 ⤳ (∅, ∅) ∗
        dlma ⤇ dl_reserved_server_socket_interp ∗
        (* preconditions to start a client proxy for the database. *)
        ⌜dba ∈ A⌝ ∗
        ⌜clt_01 ∉ A⌝ ∗
        dba ⤇ leader_si ∗
        clt_01 ⤳ (∅, ∅) ∗
        free_ports (ip_of_address clt_01) {[port_of_address clt_01]}
    }}}
      node0 #clt_00 #clt_01 #dlma #dba @[ip_of_address clt_00]
    {{{ RET #(); True }}}.
  Proof.
  Admitted.

End proof_of_the_node_0.


(* -------------------------------------------------------------------------- *)
(** The proof of the node 1 (reader) *)
(* -------------------------------------------------------------------------- *)
Section proof_of_the_node_1.
  Context `{!anerisG Mdl Σ, !lockG Σ}.
  Context (dba dbFa dlma : socket_address).
  Notation DBP := (DBSrv dba dbFa).
  (* Leader-Followers top-level resources. *)
  Context `{TM: !DB_time, !DBG Σ}.
  (* Context `{DBP: !DB_params}. *)
  Context `{!@DB_resources _ _ _ _ DBP }.
  Notation DLRes := (SharedRes DBP).
  (* Distributed Lock top-level resources. *)
  Context `{!DlockG Σ}.
  Context (DBL := (DLSrv dlma)).
  Context `{!DL_resources}.
  Context (leader_si : message → iProp Σ).
  Context (HstartProxySpec :
            ⊢ (∀ A ca, @init_client_proxy_leader_spec _ _ _ _ DBP _ A ca leader_si)).
  Context (HsubscribeClient :
            ⊢ (∀ sa (A : gset socket_address),
                 @dl_subscribe_client_spec _ _ _ DBL _ DLRes sa A)).

  Lemma proof_of_node1 (clt_10 clt_11 : socket_address) (A : gset socket_address) :
    ip_of_address clt_10 = ip_of_address clt_11 →
    {{{
        (* preconditions for subscribing client to dlock. *)
        ⌜clt_10 ∉ A⌝ ∗
        fixed A ∗
        free_ports (ip_of_address clt_10) {[port_of_address clt_10]} ∗
        clt_10 ⤳ (∅, ∅) ∗
        dlma ⤇ dl_reserved_server_socket_interp ∗
        (* preconditions to start a client proxy for the database. *)
        ⌜dba ∈ A⌝ ∗
        ⌜clt_11 ∉ A⌝ ∗
        dba ⤇ leader_si ∗
        clt_11 ⤳ (∅, ∅) ∗
        free_ports (ip_of_address clt_11) {[port_of_address clt_11]}
    }}}
      node0 #clt_10 #clt_11 #dlma #dba @[ip_of_address clt_10]
    {{{ RET #(); True }}}.
  Proof.
  Admitted.

End proof_of_the_node_1.

(* -------------------------------------------------------------------------- *)
(** The proof of adequacy. *)
(* -------------------------------------------------------------------------- *)
Section proof_of_adequacy.
(* TODO. *)
End proof_of_adequacy.
