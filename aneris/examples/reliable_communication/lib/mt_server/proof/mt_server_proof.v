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
  Context `{!MTS_user_params}.

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
     RCParams_srv_N := MTS_mN;
  |}.

  Context `{cmh: !@Chan_mapsto_resource Σ}.
  Context `{SnRes : !SessionResources MT_UP}.
  Context `{HspecS : !Reliable_communication_Specified_API_session cmh}.
  Context `{HspecN : !Reliable_communication_Specified_API_network MT_UP SnRes}.
  Context `{!MTS_spec_params}.

  Lemma service_loop_proof (c : val) :
    {{{ is_monitor MTS_mN (ip_of_address MTS_saddr) MTS_mγ MTS_mv MTS_mR ∗
        c ↣{ ip_of_address MTS_saddr, MTS_rep_ser } iProto_dual req_prot  }}}
      service_loop c MTS_mv MTS_handler #() @[ip_of_address MTS_saddr]
    {{{ RET #(); ⌜True⌝  }}}.
  Proof.
    iIntros (Φ) "(#Hlk & Hc) HΦ". rewrite /service_loop.
    do 10 wp_pure _.
    iLöb as "IH".
    wp_pures.
    rewrite /req_prot. rewrite /req_prot_aux.
    simpl in *.
    wp_recv (reqv reqd) as "HreqPre".
    wp_pures.
    wp_apply (monitor_acquire_spec with "[Hlk]"); first by iFrame "#".
    iIntros (v) "(-> & HKey & HR)".
    wp_pures.
    wp_apply (MTS_handler_spec with "[$Hlk $HKey $HR $HreqPre]").
    iIntros (repv repd) "(%Hser & HKey & HR & HreqPost)".
    wp_pures.
    wp_apply (monitor_release_spec with "[$Hlk $HR $HKey]").
    iIntros (v ->).
    do 2 wp_pure _.
    wp_send with "[$HreqPost]".
    do 2 wp_pure _.
    by iApply ("IH" with "[$Hc]").
  Qed.

  Lemma wp_accept_new_connections_loop skt  :
    {{{ MTS_saddr ⤇ reserved_server_socket_interp ∗
        SrvListens skt ∗
        is_monitor MTS_mN (ip_of_address MTS_saddr) MTS_mγ MTS_mv MTS_mR }}}
      accept_new_connections_loop skt MTS_mv MTS_handler #()
      @[ip_of_address RCParams_srv_saddr]
    {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "(#Hsi & Hlistens & #Hlk) HΦ".
    rewrite /accept_new_connections_loop.
    do 10 (wp_pure _).
    iLöb as "IH".
    wp_pure _.
    wp_smart_apply (RCSpec_accept_spec with "[$Hlistens]").
    iIntros (c clt_addr v) "(-> & Hlistens & Hc)".
    wp_pures.
    wp_apply (aneris_wp_fork with "[-]").
    iSplitL "Hlistens".
    - iNext.
      do 2 wp_pure _.
      iApply ("IH" with "[$Hlistens]").
      by iIntros.
    - iNext.
      wp_pures.
      simpl in *.
      by wp_apply (service_loop_proof with "[$Hlk $Hc]").
  Qed.

  Definition run_server_internal_spec A : iProp Σ :=
    {{{ ⌜MTS_saddr ∈ A⌝ ∗
        fixed A ∗
        free_ports (ip_of_address MTS_saddr) {[port_of_address MTS_saddr]} ∗
        MTS_saddr ⤇ reserved_server_socket_interp ∗
        MTS_saddr ⤳ (∅, ∅) ∗
        SrvInit ∗
        is_monitor MTS_mN (ip_of_address MTS_saddr) MTS_mγ MTS_mv MTS_mR }}}
      run_server
        (s_serializer MTS_rep_ser)
        (s_serializer MTS_req_ser)
        #MTS_saddr
        MTS_mv
        MTS_handler
        @[ip_of_address MTS_saddr]
    {{{ RET #(); ⌜True⌝ }}}.

  Lemma run_server_internal_spec_holds A : ⊢ run_server_internal_spec A.
  Proof.
    iIntros (Φ) "!#".
    iIntros "Hres HΦ".
    iDestruct "Hres" as "(#HA & #Hf & Hfp & #Hsi & Hmh & Hinit & #Hmon)".
    rewrite /run_server.
    wp_pures.
    wp_apply (RCSpec_make_server_skt_spec with "[$HA $Hmh $Hsi $Hf $Hinit $Hfp][HΦ]").
    iNext. iIntros (skt) "Hcl".
    wp_pures.
    wp_apply (RCSpec_server_listen_spec with "[$Hcl][HΦ]").
    iNext. iIntros (v) "(-> & Hp)".
    wp_pures.
    wp_apply aneris_wp_fork.
    iSplitL "HΦ".
    - iNext; by iApply "HΦ".
    - by iApply (wp_accept_new_connections_loop with "[$]").
  Qed.

  Definition make_request_spec_internal (handler : val) clt_addr : iProp Σ :=
    ∀ reqv reqd,
    {{{ ⌜Serializable MTS_req_ser reqv⌝ ∗ MTS_handler_pre reqv reqd }}}
      handler reqv @[ip_of_address clt_addr]
    {{{ repd repv, RET repv; MTS_handler_post repv reqd repd  }}}.

  Lemma make_request_spec_internal_holds c lk γlk sa :
    {{{  is_lock (MTS_mN.@"proxy") (ip_of_address sa) γlk lk
            (c ↣{ip_of_address sa,RCParams_clt_ser} RCParams_protocol) }}}
      make_request c lk @[ip_of_address sa]
    {{{ reqh, RET reqh; make_request_spec_internal reqh sa }}}.
  Proof.
    iIntros (Φ) "#Hlk HΦ".
    rewrite /make_request.
    wp_pures.
    iApply "HΦ".
    rewrite /make_request_spec_internal.
    iIntros (reqv reqd) "!#".
    iIntros (Ψ) "(%Hser & HreqPre) HΨ".
    wp_pures.
    wp_apply (acquire_spec with "[$Hlk]").
    iIntros (v) "(-> & HKey & HR)".
    wp_pures.
    wp_send with "[$HreqPre]".
    wp_pures.
    wp_recv (repv repd) as "HreqPost".
    wp_pures.
    wp_apply (release_spec with "[$Hlk $HR $HKey]").
    iIntros (v ->).
    wp_pures.
    by iApply "HΨ".
  Qed.

  Definition init_client_proxy_internal_spec A sa : iProp Σ :=
    {{{ ⌜sa ∉ A⌝ ∗
        fixed A ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} ∗ sa ⤳ (∅, ∅) ∗
        MTS_saddr ⤇ reserved_server_socket_interp }}}
      init_client_proxy
        (s_serializer MTS_req_ser)
        (s_serializer MTS_rep_ser)
        #sa
        #MTS_saddr
       @[ip_of_address sa]
    {{{ reqh, RET reqh; make_request_spec_internal reqh sa }}}.

  Lemma init_client_proxy_internal_spec_holds A sa : ⊢ init_client_proxy_internal_spec A sa.
  Proof.
    iIntros (Φ) "!#".
    iIntros "(#HnA & #Hf & Hfp & Hmh & #Hsi) HΦ".
    rewrite /init_client_proxy.
    wp_pures.
    wp_apply (RCSpec_make_client_skt_spec with "[$HnA $Hmh $Hsi $Hf $Hfp][HΦ]").
    iNext.
    iIntros (skt) "Hcl".
    wp_pures.
    wp_apply (RCSpec_connect_spec with "[$Hcl][HΦ]").
    iNext. iIntros (c) "Hcl". wp_pures.
    wp_apply (newlock_spec
                (MTS_mN .@ "proxy") _
                ( c ↣{ip_of_address sa,RCParams_clt_ser} RCParams_protocol) with "[$Hcl]").
    iIntros (lk γlk) "#Hlk".
    wp_pures.
    by wp_apply (make_request_spec_internal_holds c lk γlk with "[$Hlk]").
  Qed.

End MTS_proof_of_code.

From aneris.examples.reliable_communication.lib.mt_server.spec Require Import api_spec.

Section MTS_proof_of_init.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{MTU : !MTS_user_params}.
  Context `{!Reliable_communication_init}.
  (* Context `{!MTS_spec_params}. *)

  Lemma MTS_init_setup_holds (E : coPset) :
    ↑MTS_mN ⊆ E →
    True ⊢ |={E}=> ∃ (srv_si : message → iProp Σ) (SrvInit : iProp Σ),
    SrvInit ∗
    ∀ (MTS : @MTS_spec_params _ _ _ _ MTU),
      (∀ A, run_server_spec SrvInit srv_si A) ∗
      (∀ A sa, init_client_proxy_spec srv_si A sa).
  Proof.
    iIntros (HE _).
    iMod (Reliable_communication_init_setup E MT_UP HE $! ⊤)
      as (chn sgn) "(Hinit & Hspecs)".
    iDestruct "Hspecs"
      as "(
           %HmkClt & %HmkSrv
         & %Hconnect
         & %Hlisten & %Haccept
         & %Hsend & %HsendTele
         & %HtryRecv & %Hrecv)".
    Unshelve. 2: { done. }
    iExists reserved_server_socket_interp, SrvInit.
    iFrame.
    iModIntro.
    iIntros (MTS).
    iSplitL.
    - iIntros (A Φ) "!#".
      iIntros "(#Hsi & HinA & Hf & Hmh & Hfp & Hinit & #Hmon) HΦ".
      iDestruct run_server_internal_spec_holds as "#HserviceSpec".
      iApply ("HserviceSpec" with "[$HinA $Hf $Hfp $Hsi $Hmon $Hmh $Hinit][$]").
      Unshelve.
      + done.
      + split; done.
      + split; done.
    - iIntros (A sa Φ) "!#".
      iIntros "(HinA & Hf & Hfp & Hmh & #Hsi) HΦ".
      iDestruct (init_client_proxy_internal_spec_holds) as "#HclientSpec".
      by iApply ("HclientSpec" with "[$HinA $Hf $Hfp $Hmh $Hsi][HΦ]").
      Unshelve.
      + done.
      + split; try done.
      + split; try done.
  Qed.


End MTS_proof_of_init.

Section MTS_proof_of_the_init_class.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{!MTS_user_params}.
  Context `{!Reliable_communication_init}.

  Global Instance mts_init : MTS_init.
  Proof.
    split. iIntros (E MTU HE _).
    iMod (MTS_init_setup_holds E HE $! ⊤) as (srv_si SrvInit) "Hinit".
    iModIntro.
    iExists _, _.
    iFrame.
    Unshelve. done.
  Qed.

End MTS_proof_of_the_init_class.
