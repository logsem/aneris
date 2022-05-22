From aneris.aneris_lang Require Import lang.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.aneris_lang.lib
     Require Import lock_proof monitor_proof serialization_proof.
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params mt_server_code.

Section Spec.
  Context `{ !anerisG Mdl Σ, !lockG Σ}.
  Context `{ !MTS_spec_params}.
  Context ( srv_si : message → iProp Σ).
  Notation srv_ip := (ip_of_address MTS_saddr).

(* Val run_server :
   'repl serializer -> 'req serializer -> saddr -> monitor -> (monitor -> 'req -> 'repl) -> unit *)
 Definition run_server_spec A : iProp Σ :=
   {{{ MTS_saddr ⤇ srv_si ∗
       ⌜MTS_saddr ∈ A⌝ ∗
       fixed A ∗
       MTS_saddr ⤳ (∅, ∅) ∗
       free_ports (srv_ip) {[port_of_address MTS_saddr]} ∗
       is_monitor MTS_mN srv_ip MTS_mγ MTS_mv MTS_mR }}}
     run_server
        (s_serializer MTS_req_ser)
        (s_serializer MTS_rep_ser)
        #MTS_saddr
        MTS_mv
        MTS_handler
       @[srv_ip]
   {{{ RET #(); ⌜True⌝ }}}.

 Definition make_request_spec (handler : val) clt_addr reqv reqd : iProp Σ :=
   {{{ ⌜Serializable MTS_req_ser reqv⌝ ∗
       MTS_handler_pre reqv reqd }}}
     handler reqv @[ip_of_address clt_addr]
   {{{ repd repv, RET repv; MTS_handler_post repv reqd repd  }}}.

(* val init_client_proxy :
   'req serializer -> 'repl serializer -> saddr -> saddr -> ('req -> 'repl) *)
 Definition init_client_proxy_spec A sa : iProp Σ :=
   {{{⌜sa ∉ A⌝ ∗
      fixed A ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗ sa ⤳ (∅, ∅) ∗
      MTS_saddr ⤇ srv_si }}}
     init_client_proxy
        (s_serializer MTS_req_ser)
        (s_serializer MTS_rep_ser)
        #MTS_saddr
        #sa
       @[ip_of_address sa]
   {{{ reqh, RET reqh; ∀ reqv reqd, make_request_spec reqh sa reqv reqd }}}.

End Spec.

Section MTS_Init.
  Context `{ !anerisG Mdl Σ, !lockG Σ}.

  Class MTS_init := {
    MTS_init_setup E (DLP : MTS_spec_params) :
    ↑MTS_mN ⊆ E →
    True ⊢ |={E}=> ∃ (srv_si : message → iProp Σ),
      (∀ A, run_server_spec srv_si A) ∗
      (∀ A sa, init_client_proxy_spec srv_si A sa) }.

End MTS_Init.
