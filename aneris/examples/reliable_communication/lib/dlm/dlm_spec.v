From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import
     list_proof pers_socket_proto serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.spec Require Import resources.
From aneris.examples.reliable_communication.lib.dlm Require Import dlm_code dlm_prelude.

Class DL_resources `{!anerisG Mdl Σ} := {
    DLockCanAcquire : socket_address → val → iProp Σ → iProp Σ;
    DLockCanRelease : socket_address → val → iProp Σ → iProp Σ;
    dl_locked : iProp Σ;
    dl_locked_exclusive : dl_locked -∗ dl_locked -∗ False;
    dl_locked_timeless :> Timeless (dl_locked);
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
    ∀ A,
    {{{ ⌜srv_sa ∈ A⌝ ∗ fixed A ∗ free_ports srv_ip {[srv_port]} ∗
        srv_sa ⤳ (∅, ∅) ∗
        srv_sa ⤇ dl_reserved_server_socket_interp ∗
        R ∗ dl_service_init }}}
      dlock_start_service #srv_sa @[srv_ip]
    {{{ RET #(); True }}}.

  Definition dl_acquire_spec (sa : socket_address) (dl : val) : iProp Σ :=
    {{{ DLockCanAcquire sa dl R  }}}
       dlock_acquire dl @[ip_of_address sa]
     {{{ RET #(); DLockCanRelease sa dl R ∗ dl_locked ∗ R }}}.

  Definition dl_release_spec (sa : socket_address) (dl : val) : iProp Σ :=
    {{{ DLockCanRelease sa dl R ∗ dl_locked ∗ R }}}
       dlock_release dl @[ip_of_address sa]
    {{{ RET #(); DLockCanAcquire sa dl R }}}.

  Definition dl_subscribe_client_spec : iProp Σ :=
    ∀ (sa : socket_address) A,
    {{{ ⌜sa ∉ A⌝ ∗ ⌜DL_server_addr ∈ A⌝ ∗ fixed A ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} ∗ sa ⤳ (∅, ∅) ∗
         DL_server_addr ⤇ dl_reserved_server_socket_interp }}}
      dlock_subscribe_client #sa #srv_sa @[ip_of_address sa]
      {{{ dl, RET dl; DLockCanAcquire sa dl R ∗
                      dl_acquire_spec sa dl ∗ dl_release_spec sa dl }}}.

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
