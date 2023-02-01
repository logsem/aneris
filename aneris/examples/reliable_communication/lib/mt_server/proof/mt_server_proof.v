From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import lock_proof set_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import tactics proofmode.
From actris.channel Require Export proto.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.examples.reliable_communication Require Import user_params.
From aneris.examples.reliable_communication.spec
     Require Import resources proofmode api_spec.
From aneris.examples.reliable_communication.lib.mt_server
     Require Import mt_server_code user_params.

Import mt_server_code.
Import monitor_proof.
Import lock_proof.
Import client_server_code.

Section MTS_proof_of_code.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{MTU : !MTS_user_params}.

  Definition req_prot_aux (rec : iProto Σ)  : iProto Σ :=
    (<! (reqv : val) (reqd : MTS_req_data) >
       MSG reqv {{ MTS_handler_pre reqv reqd }} ;
     <? (repv : val) (repd : MTS_rep_data) >
       MSG repv {{ MTS_handler_post repv reqd repd }};
     rec)%proto.

  Instance req_prot_aux_contractive : Contractive (req_prot_aux).
  Proof. solve_proto_contractive. Qed.
  Definition req_prot : iProto Σ := fixpoint (req_prot_aux).
  Global Instance req_prot_unfold :
    ProtoUnfold req_prot (req_prot_aux req_prot).
  Proof. apply proto_unfold_eq, fixpoint_unfold. Qed.

  Global Instance MT_UP : Reliable_communication_service_params :=
  {| RCParams_clt_ser := MTS_req_ser;
     RCParams_srv_ser := MTS_rep_ser;
     RCParams_srv_ser_inj := MTS_rep_ser_inj;
     RCParams_srv_ser_inj_alt := MTS_rep_ser_inj_alt;
     RCParams_clt_ser_inj := MTS_req_ser_inj;
     RCParams_clt_ser_inj_alt := MTS_req_ser_inj_alt;
     RCParams_srv_saddr := MTS_saddr;
     RCParams_protocol := req_prot;
  |}.

  Context `{cmh: !@Chan_mapsto_resource Σ}.
  Context `{SnRes : !SessionResources MT_UP}.
  Context `{HspecS : !Reliable_communication_Specified_API_session cmh}.
  Context `{HspecN : !Reliable_communication_Specified_API_network MT_UP SnRes}.

  Lemma service_loop_proof (c handler : val) :
    handler_spec (handler : val) -∗
    {{{ c ↣{ ip_of_address MTS_saddr, MTS_rep_ser } iProto_dual req_prot }}}
      service_loop c handler #() @[ip_of_address MTS_saddr]
    {{{ RET #(); ⌜True⌝  }}}.
  Proof.
    iIntros "#Hhandler" (Φ) "!> Hc HΦ". rewrite /service_loop.
    wp_pures.
    iLöb as "IH".
    wp_pures.
    rewrite /req_prot. rewrite /req_prot_aux.
    simpl in *.
    wp_recv (reqv reqd) as "HreqPre".
    wp_pures.
    wp_apply ("Hhandler" with "HreqPre").
    iIntros (repv repd) "(%Hser & HreqPost)".
    wp_pures.
    wp_send with "[$HreqPost]".
    wp_pures.
    by iApply ("IH" with "[$Hc]").
  Qed.

  Lemma wp_accept_new_connections_loop skt handler :
    handler_spec (handler : val) -∗
    {{{ MTS_saddr ⤇ reserved_server_socket_interp ∗
        SrvListens skt }}}
      accept_new_connections_loop skt handler #()
      @[ip_of_address RCParams_srv_saddr]
    {{{ RET #(); False }}}.
  Proof.
    iIntros "#Hhandler" (Φ) "!> (#Hsi & Hlistens) HΦ".
    rewrite /accept_new_connections_loop.
    wp_pures.
    iLöb as "IH".
    wp_smart_apply (RCSpec_accept_spec with "Hlistens").
    iIntros (c clt_addr) "(Hlistens & Hc)".
    wp_pures.
    wp_apply (aneris_wp_fork with "[-]").
    iSplitL "Hlistens".
    - iNext.
      wp_pures.
      iApply ("IH" with "[$Hlistens]").
      by iIntros.
    - iNext.
      wp_pures.
      simpl in *.
      by wp_apply (service_loop_proof with "Hhandler Hc").
  Qed.

  Definition run_server_internal_spec handler : iProp Σ :=
    handler_spec handler -∗
    {{{ free_ports (ip_of_address MTS_saddr) {[port_of_address MTS_saddr]} ∗
        MTS_saddr ⤇ reserved_server_socket_interp ∗
        MTS_saddr ⤳ (∅, ∅) ∗
        SrvInit }}}
      run_server
        (s_serializer MTS_rep_ser)
        (s_serializer MTS_req_ser)
        #MTS_saddr
        handler
        @[ip_of_address MTS_saddr]
    {{{ RET #(); ⌜True⌝ }}}.

  Lemma run_server_internal_spec_holds handler :
    ⊢ run_server_internal_spec handler.
  Proof.
    iIntros "#Hhandler" (Φ) "!>".
    iIntros "Hres HΦ".
    iDestruct "Hres" as "(Hfp & #Hsi & Hmh & Hinit)".
    rewrite /run_server.
    wp_pures.
    wp_apply (RCSpec_make_server_skt_spec with "[$Hmh $Hsi $Hinit $Hfp][HΦ]").
    iNext. iIntros (skt) "Hcl".
    wp_pures.
    wp_apply (RCSpec_server_listen_spec with "[$Hcl][HΦ]").
    iNext. iIntros "Hp".
    wp_pures.
    wp_apply aneris_wp_fork.
    iSplitL "HΦ".
    - iNext; by iApply "HΦ".
    - by iApply (wp_accept_new_connections_loop with "Hhandler [$]").
  Qed.

  Definition make_request_spec_internal : iProp Σ :=
    ∀ ip (c : val) reqv reqd,
    {{{ c ↣{ip,RCParams_clt_ser} RCParams_protocol ∗
        ⌜Serializable MTS_req_ser reqv⌝ ∗ MTS_handler_pre reqv reqd }}}
      make_request c reqv @[ip]
    {{{ repd repv, RET repv;
          c ↣{ip,RCParams_clt_ser} RCParams_protocol ∗
          MTS_handler_post repv reqd repd  }}}.

  Lemma make_request_spec_internal_holds :
    ⊢ make_request_spec_internal.
  Proof.
    iIntros (ip c reqv reqd) "!>".
    iIntros (Φ) "(Hc & %Hser & HP) HΦ".
    rewrite /make_request.
    rewrite /RCParams_protocol /=.
    wp_pures.
    wp_send with "[$HP]".
    wp_recv (repv repd) as "HQ".
    iApply "HΦ". by iFrame.
  Qed.

  Definition init_client_proxy_internal_spec sa : iProp Σ :=
    {{{ unallocated {[sa]} ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} ∗ sa ⤳ (∅, ∅) ∗
        MTS_saddr ⤇ reserved_server_socket_interp }}}
      init_client_proxy
        (s_serializer MTS_req_ser)
        (s_serializer MTS_rep_ser)
        #sa
        #MTS_saddr
       @[ip_of_address sa]
    {{{ c, RET c;
          c ↣{ip_of_address sa,RCParams_clt_ser} RCParams_protocol }}}.

  Lemma init_client_proxy_internal_spec_holds sa :
    ⊢ init_client_proxy_internal_spec sa.
  Proof.
    iIntros (Φ) "!#".
    iIntros "(Hf & Hfp & Hmh & #Hsi) HΦ".
    rewrite /init_client_proxy.
    wp_pures.
    wp_apply (RCSpec_make_client_skt_spec with "[$Hmh $Hsi $Hf $Hfp][HΦ]").
    iNext.
    iIntros (skt) "Hcl".
    wp_pures.
    wp_apply (RCSpec_connect_spec with "[$Hcl][HΦ]").
    iNext. iIntros (c) "Hcl". wp_pures.
    wp_pures.
    by iApply "HΦ".
  Qed.

  Global Instance mtsri : MTS_resources := {
    MTSCanRequest ip rpc := rpc ↣{ip,RCParams_clt_ser} RCParams_protocol }.

End MTS_proof_of_code.

From aneris.examples.reliable_communication.spec
     Require Import ras.
From aneris.examples.reliable_communication.instantiation
     Require Import instantiation_of_init.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.

Section MTS_proof_of_init.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{MTU : !MTS_user_params, !SpecChanG Σ}.

  Lemma MTS_init_setup_holds (E : coPset) :
    ⊢ |={E}=> ∃ (srv_si : message → iProp Σ) (SrvInit : iProp Σ)
      (MTR : MTS_resources),
      SrvInit ∗
      (run_server_spec SrvInit srv_si) ∗
      (init_client_proxy_spec srv_si) ∗
      make_request_spec.
  Proof.
    iMod (Reliable_communication_init_setup E MT_UP)
      as (chn sgn) "(Hinit & Hspecs)".
    iDestruct "Hspecs"
      as "(
           %HmkClt & %HmkSrv
         & %Hconnect
         & %Hlisten & %Haccept
         & %Hsend & %HsendTele
         & %HtryRecv & %Hrecv)".
    iExists reserved_server_socket_interp, SrvInit, mtsri.
    iFrame.
    iModIntro.
    iSplitL.
    - iIntros "!>" (handler) "#Hhandler".
      iIntros (Φ) "!#".
      iIntros "(#Hsi & Hmh & Hfp & Hinit) HΦ".
      (* iDestruct run_server_internal_spec_holds as "#HserviceSpec". *)
      iApply (run_server_internal_spec_holds with
               "Hhandler [$Hfp $Hsi $Hmh $Hinit][$]").
      Unshelve.
      + done.
      + split; done.
      + split; done.
    - iSplitL.
      + iIntros (sa Φ) "!#".
        iIntros "(Hf & Hfp & Hmh & #Hsi) HΦ".
        iDestruct (init_client_proxy_internal_spec_holds) as "#HclientSpec".
        by iApply ("HclientSpec" with "[$Hf $Hfp $Hmh $Hsi][HΦ]").
        Unshelve.
        done.
      + iIntros (ip rpc reqv reqd Φ) "!#".
        iIntros "(Hreq & %Hser & HP) HΦ".
        iApply (make_request_spec_internal_holds with "[$Hreq $HP //]").
        by iApply "HΦ".
        Unshelve.
        done.
  Qed.

End MTS_proof_of_init.

Section MTS_proof_of_the_init_class.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{!MTS_user_params}.
  Context `{!SpecChanG Σ}.

  Global Instance mts_init : MTS_init.
  Proof.
    split. iIntros (E MTU).
    iMod (MTS_init_setup_holds E)
      as (srv_si SrvInit MTR) "(Hinit & Hspecs)".
    iModIntro.
    iExists _, SrvInit, MTR.
    iFrame.
  Qed.

End MTS_proof_of_the_init_class.
From aneris.examples.reliable_communication.instantiation Require Import
     instantiation_of_resources
     instantiation_of_client_specs
     instantiation_of_server_specs
     instantiation_of_send_and_recv_specs.
