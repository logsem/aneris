From aneris.aneris_lang Require Import lang.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.aneris_lang.lib
     Require Import lock_proof monitor_proof serialization_proof.
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params mt_server_code.

Section Spec.
  Context `{ !anerisG Mdl Σ, !lockG Σ}.
  Context `{ MTU: !MTS_user_params }.
  Context `{ MTR: !MTS_resources }.
  Context (SrvInit : iProp Σ).
  Context (srv_si : message → iProp Σ).
  Notation srv_ip := (ip_of_address MTS_saddr).

  Definition run_server_spec : iProp Σ :=
    □ ∀ handler,
    handler_spec handler -∗
    {{{ MTS_saddr ⤇ srv_si ∗
        MTS_saddr ⤳ (∅,∅) ∗
        free_ports (srv_ip) {[port_of_address MTS_saddr]} ∗
        SrvInit }}}
      run_server
        (s_serializer MTS_rep_ser)
        (s_serializer MTS_req_ser)
        #MTS_saddr
        handler
       @[srv_ip]
    {{{ RET #(); True }}}.

  Definition make_request_spec : iProp Σ :=
    ∀ ip (rpc : val) reqv reqd,
    {{{ MTSCanRequest ip rpc ∗
        ⌜Serializable MTS_req_ser reqv⌝ ∗
        MTS_handler_pre reqv reqd }}}
      make_request rpc reqv @[ip]
    {{{ repd repv, RET repv;
        MTSCanRequest ip rpc ∗ MTS_handler_post repv reqd repd  }}}.

  Definition init_client_proxy_spec : iProp Σ :=
    ∀ sa,
    {{{ unallocated {[sa]} ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} ∗ sa ⤳ (∅, ∅) ∗
        MTS_saddr ⤇ srv_si }}}
      init_client_proxy
        (s_serializer MTS_req_ser)
        (s_serializer MTS_rep_ser)
        #sa
        #MTS_saddr
       @[ip_of_address sa]
    {{{ reqh, RET reqh; MTSCanRequest (ip_of_address sa) reqh }}}.

End Spec.

Section MTS_Init.
  Context `{ !anerisG Mdl Σ, !lockG Σ}.

  Class MTS_init := {
    MTS_init_setup E (MTU : MTS_user_params) :
    ↑MTS_mN ⊆ E →
    ⊢ |={E}=> ∃ (srv_si : message → iProp Σ) (SrvInit : iProp Σ)
      (MTR : MTS_resources),
      SrvInit ∗
      (run_server_spec SrvInit srv_si) ∗
      (init_client_proxy_spec srv_si) ∗
      make_request_spec }.

End MTS_Init.
