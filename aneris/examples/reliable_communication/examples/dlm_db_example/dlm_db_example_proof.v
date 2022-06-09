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
(** The definition of the resource guarded by the distributed lock manager. *)
(* -------------------------------------------------------------------------- *)
Section proof_of_code.
  Context `{!anerisG Mdl Σ, !lockG Σ}.
  Context `{TM: !DB_time, !DBG Σ}.
  Context (leader_si : message → iProp Σ).
  Context (db_sa db_Fsa dlm_sa : socket_address).

  (* ------------------------------------------------------------------------ *)
  (** The definition of the parameters for DB and DL and shared resources. *)
  (* ------------------------------------------------------------------------ *)

  Local Instance DLSrv : DL_params :=
    {|
      DL_server_addr := dlm_sa;
      DL_namespace := (nroot .@ "DLInv");
    |}.

  Local Instance DBSrv : DB_params :=
    {|
      DB_addr := db_sa;
      DB_addrF := db_Fsa;
      DB_keys := {["x"; "y"]};
      DB_InvName := (nroot .@ "DBInv");
      DB_serialization := int_serialization;
      DB_ser_inj := int_ser_is_ser_injective;
      DB_ser_inj_alt := int_ser_is_ser_injective_alt
    |}.

  Context `{!@DB_resources _ _ _ _ DBSrv}.
  Context `{!DlockG Σ, !DL_resources}.

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

  (* ------------------------------------------------------------------------ *)
  (** The proof of the internal do_writes call *)
  (* ------------------------------------------------------------------------ *)
  Section proof_of_the_do_writes.
    Context (dl : val) (clt_00 : socket_address).
    Context (wr : val) (clt_01 : socket_address).
    Context (HWriteSpec : ⊢ ∀ k v h, simplified_write_spec wr clt_01 k v h).
    Context (HAcqSpec : dl_acquire_spec SharedRes clt_00 dl).
    Context (HRelSpec : dl_release_spec SharedRes clt_00 dl).

    Lemma wp_do_writes :
      ip_of_address clt_00 = ip_of_address clt_01 →
      {{{ DLockCanAcquire clt_00 dl SharedRes }}}
        do_writes dl wr @[ip_of_address clt_00]
      {{{ RET #(); True }}}.
    Proof.
      iIntros (HipEq Φ) "Hacq HΦ".
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

  (* ------------------------------------------------------------------------ *)
  (** The proof of the internal do_reads call *)
  (* ------------------------------------------------------------------------ *)
  Section proof_of_the_do_reads.
    Context (dl : val) (clt_10 : socket_address).
    Context (rd : val) (clt_11 : socket_address).
    Context (HReadSpec : ⊢ ∀ k q h, read_spec rd clt_11 k q h).
    Context (HAcqSpec : dl_acquire_spec SharedRes clt_10 dl).
    Context (HRelSpec : dl_release_spec SharedRes clt_10 dl).

  (* NotaBene : the spec of dl_wait_on_read can be applied to
     generic key `k` and value `v` (instead of x and 37) only if
     a resource k ↦ₖ{q} v is either provided in the precondition
     or if it is also guarded by the distributed lock. *)
    Lemma wp_dl_wait_on_read :
      ip_of_address clt_10 = ip_of_address clt_11 →
      {{{ DLockCanAcquire clt_10 dl SharedRes }}}
        dl_wait_on_read dl rd #"x" #37 @[ip_of_address clt_10]
      {{{ RET #(); True }}}.
    Proof.
    Admitted.

    Lemma wp_do_reads :
      {{{ DLockCanAcquire clt_10 dl SharedRes }}}
        do_reads dl rd @[ip_of_address clt_10]
      {{{ RET #(); True }}}.
    Proof.
    Admitted.

  End proof_of_the_do_reads.

  (* ------------------------------------------------------------------------ *)
  (** The proof of the node 0 (writer) *)
  (* ------------------------------------------------------------------------ *)
  Section proof_of_the_node_0.
    Context (HdbCS : ⊢ (∀ A ca, init_client_proxy_leader_spec A ca leader_si)).
    Context (HdlCS : ⊢ (∀ sa A, dl_subscribe_client_spec SharedRes sa A)).

    Lemma proof_of_node0 (clt_00 clt_01 : socket_address) A :
    ip_of_address clt_00 = ip_of_address clt_01 →
    {{{
        (* preconditions for subscribing client to dlock. *)
        ⌜clt_00 ∉ A⌝ ∗
        fixed A ∗
        free_ports (ip_of_address clt_00) {[port_of_address clt_00]} ∗
        clt_00 ⤳ (∅, ∅) ∗
        dlm_sa ⤇ dl_reserved_server_socket_interp ∗
        (* preconditions to start a client proxy for the database. *)
        ⌜db_sa ∈ A⌝ ∗
        ⌜clt_01 ∉ A⌝ ∗
        db_sa ⤇ leader_si ∗
        clt_01 ⤳ (∅, ∅) ∗
        free_ports (ip_of_address clt_01) {[port_of_address clt_01]}
    }}}
      node0 #clt_00 #clt_01 #dlm_sa #db_sa @[ip_of_address clt_00]
    {{{ RET #(); True }}}.
  Proof.
  Admitted.

  End proof_of_the_node_0.

  (* ------------------------------------------------------------------------ *)
  (** The proof of the node 1 (reader) *)
  (* ------------------------------------------------------------------------ *)
  Section proof_of_the_node_1.
    Context (HdbCS : ⊢ (∀ A ca, init_client_proxy_leader_spec A ca leader_si)).
    Context (HdlCS : ⊢ (∀ sa A, dl_subscribe_client_spec SharedRes sa A)).

    Lemma proof_of_node1 (clt_10 clt_11 : socket_address) A :
      ip_of_address clt_10 = ip_of_address clt_11 →
      {{{
        (* preconditions for subscribing client to dlock. *)
        ⌜clt_10 ∉ A⌝ ∗
        fixed A ∗
        free_ports (ip_of_address clt_10) {[port_of_address clt_10]} ∗
        clt_10 ⤳ (∅, ∅) ∗
        dlm_sa ⤇ dl_reserved_server_socket_interp ∗
        (* preconditions to start a client proxy for the database. *)
        ⌜db_sa ∈ A⌝ ∗
        ⌜clt_11 ∉ A⌝ ∗
        db_sa ⤇ leader_si ∗
        clt_11 ⤳ (∅, ∅) ∗
        free_ports (ip_of_address clt_11) {[port_of_address clt_11]}
      }}}
        node1 #clt_10 #clt_11 #dlm_sa #db_sa @[ip_of_address clt_10]
      {{{ RET #(); True }}}.
    Proof.
    Admitted.

  End proof_of_the_node_1.

End proof_of_code.

(* From aneris.examples.reliable_communication.instantiation *)
(*      Require Import instantiation_of_init. *)


(** Concrete parameters (addresses, ips) *)
Definition db_sa := SocketAddressInet "0.0.0.0" 80.
Definition db_Fsa := SocketAddressInet "0.0.0.0" 81.
Definition dlm_sa := SocketAddressInet "0.0.0.1" 80.
Definition clt_sa00 := SocketAddressInet "0.0.0.2" 80.
Definition clt_sa01 := SocketAddressInet "0.0.0.2" 81.
Definition clt_sa10 := SocketAddressInet "0.0.0.3" 80.
Definition clt_sa11 := SocketAddressInet "0.0.0.3" 81.
Definition A : gset socket_address := {[ db_sa; db_Fsa; dlm_sa ]}.
Definition ips : gset string := {[ "0.0.0.0" ; "0.0.0.1"; "0.0.0.2"; "0.0.0.3" ]}.
Global Instance DLP : DL_params :=
    {|
      DL_server_addr := dlm_sa;
      DL_namespace := (nroot .@ "DLInv");
    |}.

Global Instance DBP : DB_params :=
    {|
      DB_addr := db_sa;
      DB_addrF := db_Fsa;
      DB_keys := {["x"; "y"]};
      DB_InvName := (nroot .@ "DBInv");
      DB_serialization := int_serialization;
      DB_ser_inj := int_ser_is_ser_injective;
      DB_ser_inj_alt := int_ser_is_ser_injective_alt
    |}.

Definition main : expr :=
    Start "0.0.0.0" (init_leader (DB_serialization.(s_serializer)) #DB_addr);;
    Start "0.0.0.1" (dlock_start_service #dlm_sa) ;;
    Start "0.0.0.2" (node0 #clt_sa00 #clt_sa01 #dlm_sa #db_sa).

Section proof_of_main.
  Context `{!anerisG Mdl Σ}.
  Context `{TM: !DB_time, !DBG Σ}.
  Context (leader_si leaderF_si : message → iProp Σ).
  Context (Init_leader : iProp Σ).
  Context `{!DlockG Σ, !DL_resources}.
  Context `{DBRes : !@DB_resources _ _ _ _ DBP}.
  Notation SharedRes := (@SharedRes _ _ _ _ db_sa db_Fsa DBRes).
  Context (HdlSrvSpec : ⊢ (∀ A, dl_server_start_service_spec SharedRes A)).
  Context (HdlCltSpec : ⊢ (∀ sa A, dl_subscribe_client_spec SharedRes sa A)).
  Context (HdbSrvSpec : ⊢ (∀ A, init_leader_spec A Init_leader leader_si leaderF_si)).
  Context (HdbCltSpec : ⊢ (∀ A ca,  init_client_proxy_leader_spec A ca leader_si)).

  Lemma main_spec :
    ⊢ |={⊤}=>
         db_sa ⤇ leader_si -∗
         db_Fsa ⤇ leaderF_si -∗
         dlm_sa ⤇ dl_reserved_server_socket_interp -∗
         fixed A -∗
         free_ip "0.0.0.0" -∗
         free_ip "0.0.0.1" -∗
         free_ip "0.0.0.2" -∗
         free_ip "0.0.0.3" -∗
         SocketAddressInet "0.0.0.0" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.0" 81 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.1" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.2" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.2" 81 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.3" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.3" 81 ⤳ (∅, ∅) -∗
         dl_service_init -∗
         Init_leader -∗
         WP main @["system"]
      {{ v, True }}.
  Proof.
  Admitted.

End proof_of_main.

(* -------------------------------------------------------------------------- *)
(** The proof of adequacy. *)
(* -------------------------------------------------------------------------- *)

Definition init_state :=
  {|
    state_heaps := {[ "system" := ∅ ]};
    state_sockets := {[ "system" := ∅ ]};
    state_ports_in_use :=
      <["0.0.0.0" := ∅ ]> $
      <["0.0.0.1" := ∅ ]> $
      <["0.0.0.2" := ∅ ]> $
      <["0.0.0.3" := ∅ ]> $ ∅;
    state_ms := ∅;
  |}.

Definition fixed_dom : gset socket_address := {[ db_sa; db_Fsa; dlm_sa ]}.

Definition dummy_model := model unit (fun x y => True) ().

Lemma dummy_model_finitary : adequacy.aneris_model_rel_finitary dummy_model.
Proof.
 intros st.
 intros f Hnot.
 pose proof (Hnot 0%nat 1%nat) as H.
 assert (0%nat = 1%nat -> False) as Himpl. {
   intros Heq.
   discriminate Heq.
 }
 apply Himpl; apply H.
 destruct (f 0%nat) as [s0 r0].
 destruct (f 1%nat) as [s1 r1].
 destruct s0, s1, st, r0, r1.
 reflexivity.
Qed.

From aneris.aneris_lang.program_logic Require Import aneris_adequacy.
From aneris.examples.reliable_communication.lib.repdb
     Require Import model.

Definition socket_interp `{!anerisG empty_model Σ}
  db_si dbF_si dlm_si sa : socket_interp Σ :=
  (match sa with
   | SocketAddressInet "0.0.0.0" 80 =>  db_si
   | SocketAddressInet "0.0.0.0" 81 =>  dbF_si
   | SocketAddressInet "0.0.0.1" 80 =>  dlm_si

   | _ => λ msg, ⌜True⌝
   end)%I.

Theorem adequacy : aneris_adequate main "system" init_state (λ _, True).
Proof.
  set (Σ := #[anerisΣ dummy_model; DBΣ]).
  eapply (@adequacy
            Σ dummy_model _ _ ips fixed_dom
            {[db_sa; db_Fsa; clt_sa00; clt_sa01; clt_sa10; clt_sa11]} ∅ ∅ ∅);
    try done; last first.
  { set_solver. }
  { intros i. rewrite /ips !elem_of_union !elem_of_singleton.
    intros [|]; subst; simpl; set_solver. }
  { rewrite /ips /= !dom_insert_L dom_empty_L right_id_L //. set_solver. }
  iIntros (Hdg) "".
  2:{ apply dummy_model_finitary . }
  admit.
Admitted.
