From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import
     list_proof pers_socket_proto serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.spec Require Import resources.
From aneris.examples.reliable_communication.lib.dlm Require Import dlm_code dlm_prelude.

Class DL_resources `{!anerisG Mdl Σ} := {
    DLockCanAcquire : ip_address → val → iProp Σ → iProp Σ;
    DLockCanRelease : ip_address → val → iProp Σ → iProp Σ;
    dl_service_init : iProp Σ;
    dl_service_init_exclusive : dl_service_init -∗ dl_service_init -∗ False;
    dl_service_init_timeless :> Timeless (dl_service_init);
    dl_reserved_server_socket_interp : message → iProp Σ;
  }.

Section DL_spec.
  Context `{!anerisG Mdl Σ, !DL_params, !DL_resources}.
  Context (R : iProp Σ).

  Notation srv_sa := DL_server_addr.
  Notation srv_ip := (ip_of_address DL_server_addr).
  Notation srv_port := (port_of_address DL_server_addr).

  Definition dl_server_start_service_spec : iProp Σ :=
    {{{ free_ports srv_ip {[srv_port]} ∗
        srv_sa ⤳ (∅, ∅) ∗
        srv_sa ⤇ dl_reserved_server_socket_interp ∗
        R ∗ dl_service_init }}}
      dlock_start_service #srv_sa @[srv_ip]
    {{{ RET #(); True }}}.

  Definition dl_acquire_spec (ip : ip_address) (dl : val) : iProp Σ :=
    {{{ DLockCanAcquire ip dl R  }}}
       dlock_acquire dl @[ip]
     {{{ RET #(); DLockCanRelease ip dl R ∗ R }}}.

  Definition dl_release_spec (ip : ip_address) (dl : val) : iProp Σ :=
    {{{ DLockCanRelease ip dl R ∗ R }}}
       dlock_release dl @[ip]
    {{{ RET #(); DLockCanAcquire ip dl R }}}.

  Definition dl_subscribe_client_spec : iProp Σ :=
    ∀ (sa : socket_address),
    {{{ unallocated {[sa]} ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} ∗ sa ⤳ (∅, ∅) ∗
         DL_server_addr ⤇ dl_reserved_server_socket_interp }}}
      dlock_subscribe_client #sa #srv_sa @[ip_of_address sa]
      {{{ dl, RET dl; DLockCanAcquire (ip_of_address sa) dl R ∗
                      dl_acquire_spec (ip_of_address sa) dl ∗
                      dl_release_spec (ip_of_address sa) dl }}}.

End DL_spec.

Section Init.
  Context `{!anerisG Mdl Σ, !DlockG Σ}.

  Class DL_init := {
    DL_init_setup E (DLP : DL_params) (R: iProp Σ):
    ↑DL_namespace ⊆ E →
    ⊢ |={E}=> ∃ (DLRS : DL_resources),
      dl_service_init ∗
        (dl_server_start_service_spec R) ∗
        (dl_subscribe_client_spec R)
    }.

End Init.
