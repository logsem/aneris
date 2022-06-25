From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang Require Import ast tactics.
From iris.algebra.lib Require Import excl_auth.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_proof.
From aneris.aneris_lang.lib Require Import lock_proof queue_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.resources Require Import
     chan_session_resources socket_interp.
From aneris.examples.reliable_communication.proof.client Require Import client_resources.

Section Proof_of_connect_step_1.
  Context `{!anerisG Mdl Σ,
            !Reliable_communication_service_params,
            !chanG Σ,
            !lockG Σ}.
  Context `{!server_ghost_names}.


  (* Just inversion lemma. *)
  Definition conn_step_1_init clt_addr (R : gset message) : iProp Σ :=
   ∀ m', (∃ cookie : nat,
        ⌜s_is_ser (msg_serialization RCParams_srv_ser)
         (InjLV (#"INIT-ACK", #cookie)) (m_body m')⌝ ∗
        ⌜m_sender m' = RCParams_srv_saddr⌝ ∗
        ⌜m_destination m' = clt_addr⌝ ∗
        CookieRes clt_addr cookie ∗
         (∃ γs, session_token clt_addr γs)) -∗
        client_interp m'.

  Lemma conn_step_1_init_holds clt_addr R : ⊢ conn_step_1_init clt_addr R.
  Proof.
    iIntros (m') "Hm'".
    iDestruct "Hm'" as (ck Hprod Hsender Hdst) "(Hck & (%γs & Htk))".
    iExists (InjLV (#"INIT-ACK", #ck)).
    iSplit; first done. iSplit; eauto. iLeft.
    iExists _, _. iSplit; first eauto. iExists ck, γs; subst; iFrame "#∗". iSplit; first eauto.
    iLeft. iSplit; first done. subst; eauto with iFrame.
  Qed.

  Lemma conn_step_1_server_interp_holds clt_addr s1 s (R : gset message) :
    ⌜s_is_ser (msg_serialization RCParams_clt_ser) (InjLV (#"INIT", #0%nat)) s1⌝ ∗
    RCParams_srv_saddr ⤇ server_interp ∗
    clt_addr ⤇ client_interp -∗
    server_interp {| m_sender := clt_addr;
                    m_destination := RCParams_srv_saddr;
                    m_protocol := sprotocol s; m_body := s1 |}.
  Proof.
    iIntros "(%Hser & #Hsrv_si & #Hclt_si)".
    iExists (InjLV (#"INIT", #0%nat)). simpl. iFrame "Hclt_si".
    iSplit; first done. iLeft. iExists "INIT", "INIT-ACK", 0. iSplit; first done.
    iExists _; iSplit; first done. iLeft. do 3 (iSplit; first done).
    iIntros (m') "Hm'".
    iDestruct "Hm'" as (ck Hprod Hdeser Hsender Hmsg) "(Hck & (%γs & Hγs))".
    iApply (conn_step_1_init_holds clt_addr R). iExists ck.
    do 3 (iSplit; first done).
    rewrite /CookieRes. iFrame "#∗"; eauto.
  Qed.

  Definition conn_step_1_post skt h s clt_addr (R T : gset message) : val → iProp Σ :=
    λ (v : val),
      (∃ (n : nat) (m : message) (mt : message),
          ⌜v = #n⌝ ∗
          ⌜m ∈ R⌝ ∗
          ⌜s_is_ser (msg_serialization RCParams_srv_ser) (InjLV (#"INIT-ACK", #n)) (m_body m)⌝ ∗
          ⌜(m_destination m) = clt_addr⌝ ∗
          isClientSocketInternal skt h s clt_addr false R ({[mt]} ∪ T) ∗
          CookieRes clt_addr n ∗
          conn_incoming_msg_cond_2 clt_addr R ∗
          ⌜s_is_ser (msg_serialization RCParams_clt_ser) (InjLV (#"INIT", #0)) (m_body mt)⌝ ∗
          ⌜(m_sender mt) = clt_addr⌝ ∗
          ⌜(m_destination mt) = RCParams_srv_saddr⌝)%I.

  Lemma client_conn_step_1_spec skt h s clt_addr R0 T0 :
    {{{   isClientSocketInternal skt h s clt_addr false R0 T0 ∗
          conn_incoming_msg_cond_1 clt_addr R0 ∗
          conn_incoming_msg_cond_2 clt_addr R0 ∗
          server_init_interp clt_addr "INIT" "INIT-ACK" 0
    }}}
      client_conn_step skt (#"INIT", #0)%V #"INIT-ACK" #RCParams_srv_saddr
      @[ip_of_address clt_addr]
      {{{  v, RET v;
          ∃ R1 T1, conn_step_1_post skt h s clt_addr R1 T1 v }}}.
  Proof.
    iIntros (Φ) "(HisClt & Hcnd1 & Hcnd2 & HresIn) HΦ".
    iDestruct "HisClt" as "(#Hsrv_si & HisClt & Hmh & #HmhR)".
    iDestruct "HisClt" as (Hskt Hsaddr Hsblock) "(Hh & #Hsi)".
    rewrite Hskt.
    iDestruct "HresIn" as "[(_ & _ & HresIn) | (%Habs & H2)]"; last done.
    wp_lam. wp_pures.
    (* Serialize the request. *)
    wp_apply (s_ser_spec (msg_serialization RCParams_clt_ser)).
    { eauto. iPureIntro. apply (serInit _ 0 Left). }
    iIntros (s1 Hs1). wp_pures.
    (* Send it. *)
    wp_apply (aneris_wp_send _ server_interp
               with "[$Hh $Hmh]"); [done|done|  | ].
    (* Prove the servers socket interp. *)
    { iSplit; iNext; first eauto.
      by iApply ((conn_step_1_server_interp_holds clt_addr s1 _ R0)
               with "[$Hsrv_si $Hsi]"). }
    iIntros "(Hh & Hmh)". wp_pures.
    set (mt :=  {|
                m_sender := clt_addr;
                m_destination := RCParams_srv_saddr;
                m_protocol := sprotocol s;
                m_body := s1
              |}).
    (* Listen. *)
    iDestruct "HresIn" as "(_ & HresIn)".
    iLöb as "IH" forall (Φ R0 T0) "HmhR Hcnd1 Hcnd2".
    wp_apply (resend_listen_spec
                _
                (conn_step_1_init clt_addr R0 ∗
                 conn_incoming_msg_cond_1 clt_addr R0 ∗
                 conn_incoming_msg_cond_2 clt_addr R0)
                (λ (v : val),
                   ∃ (R T : gset message),
                    conn_step_1_post skt h s clt_addr R T v)%I
                _ _ _ _ _ mt _ client_interp server_interp
               with "[] [$Hh $Hmh $Hsi $Hcnd1 $Hcnd2]");
      [done | done | done | done |  |  by iFrame "#"; iApply conn_step_1_init_holds| ].
    2:{ iIntros (v) "HQ".
        iDestruct "HQ" as (R T n0 m0 mt0) "(-> & %Hm0 & %Hser & %Hdst & HisClt & Hck & Hcnd2 & %Hmt1 & %Hmt2)".
        iDestruct "HisClt" as "(#Hsrv_si2 & HisClt & Hmh2 & #HmhR2)".
        iDestruct "HisClt" as (-> Hsaddr2 Hsblock2) "(Hh2 & #Hsi2)".
        iApply ("HΦ" $! #n0 with "[Hh2 Hmh2 HmhR2 Hck Hcnd2]"); last iFrame.
        iExists _, _. iFrame "Hcnd2". iExists n0, m0, _. iFrame "#∗"; eauto. }
    iIntros (m) "!#". iIntros (Ψ) "(%Hy1 & (Hy2 & Hcnd1 & Hcnd2) & Hy3) HΨ". wp_pures.
    iDestruct "Hy3" as "[(%Hm & Hh & Hmh & Hres)|(%Hm & Hh & Hmh)]".
    (* Case 1/2 : m ∉ R *)
    *  iDestruct (client_interp_le with "[$Hres]") as "#Hres_pers".
       iDestruct (big_sepS_insert_2 m with "Hres_pers [$HmhR Hres_pers]")
         as "#HmhRext".
       iDestruct "Hres" as (mval Hsender Hser) "Hres".
       wp_apply (s_deser_spec ((msg_serialization
                    RCParams_srv_ser))); first done.
       iIntros "_". iDestruct "Hres" as "[Hres|(#Hsmode & [Hres|Hres])]".
       (* Case 1.1/3 : mval = InjLV (#s0, #i) *)
       ** iDestruct "Hres" as (s2 i2 ->) "Hres". wp_pures.
          iDestruct "Hres" as
            (n γs Hn) "(Htk & [(%Hs & Hck)|(%Hs & Hgh)])"; rewrite Hs.
          (* Case A: the reply is INIT-ACK. *)
          (* Check whether the reply is INIT-ACK
               and #(m_sender m) = #RCParams_srv_saddr. *)
          *** case_bool_decide as Heq1; wp_pures; last done.
              (* The reply is INIT-ACK. *)
              case_bool_decide as Heq2; wp_pures.
              (* The msg is from the server *)
              **** iApply "HΨ". inversion Heq1.
                   iExists ({[m]} ∪ R0), T0.
                   iExists n, m. rewrite Hy1 Hn.
                   iExists _.
                   iSplit; first done.
                   iSplit; first eauto with set_solver.
                   rewrite Hs in Hser.
                   iSplit; first eauto.
                   iSplit; first eauto.
                   iFrame "#∗".
                   iSplit; first done.
                   iSplitL "Hcnd2".
                   iApply (conn_incoming_msg_cond_2_extend _ _ _ n); eauto.
                   rewrite Hn. iLeft. eauto.
                   done.
              **** rewrite Hsender in Heq2. done.
          (* Case B: the reply is COOKIE-ACK. *)
          (* Check whether the reply is
             INIT-ACK and #(m_sender m) = #RCParams_srv_saddr. *)
          *** wp_pures.
              (* wp_apply (aneris_wp_send_duplicate with "[$Hh $Hmh]"); *)
              (*   [done | done | set_solver | | ]. iFrame "Hsrv_si". *)
              (* iIntros "(Hh & Hmh)". wp_pures. *)
              iApply ("IH" with  "[] [HΨ] [$Hh] [Hmh] [$HmhRext] [Hcnd1]").
              { iIntros (m') "Hm'".
                iDestruct "Hm'" as (ck γs' Hser1 ? ?) "(#Htk & Hm')".
                iApply (conn_step_1_init_holds clt_addr R0 with "[Hm']").
                iExists ck. iFrame "#∗". eauto. }
              iIntros (v) "Hpost". iApply "HΨ"; subst; eauto. iFrame.
              { iFrame. iApply (conn_incoming_msg_cond_1_extend _ _ _ n); eauto.
              rewrite Hn. subst. iLeft. eauto. }
              { iApply (conn_incoming_msg_cond_2_extend _ _ _ n with "[Hgh]"); eauto.
                rewrite Hn. subst. iRight.
                iDestruct "Hgh" as (γs') "(H1 & H2)". eauto. }
       ** iDestruct "Hres" as (ackid -> n) "(-> & Hfr)". wp_pures.
          iApply ("IH" with  "[] [HΨ] [$Hh] [$Hmh] [$HmhRext] [Hcnd1]").
          { iIntros (m') "Hm'".
            iDestruct "Hm'" as (ck γs' Hser1 ? ?) "(#Htk & Hm')".
            iApply (conn_step_1_init_holds clt_addr R0 with "[Hm']").
            iExists ck. iFrame "#∗". eauto. }
          iIntros (v) "Hpost". iApply "HΨ"; subst; eauto.
          { iApply (conn_incoming_msg_cond_1_extend _ _ _ n); eauto. }
          { iApply (conn_incoming_msg_cond_2_extend _ _ _ n); eauto. }
       ** iDestruct "Hres" as (i w -> n) "(Heq & Hidmsg)". wp_pures.
          iApply ("IH" with  "[] [HΨ] [$Hh] [$Hmh] [$HmhRext] [Hcnd1]").
          { iIntros (m') "Hm'".
            iDestruct "Hm'" as (ck γs' Hser1 ? ?) "(#Htk & Hm')".
            iApply (conn_step_1_init_holds clt_addr R0 with "[Hm']").
            iExists ck. iFrame "#∗". eauto. }
          iIntros (v) "Hpost". iApply "HΨ"; subst; eauto.
          { iApply (conn_incoming_msg_cond_1_extend _ _ _ n); eauto. }
          { iApply (conn_incoming_msg_cond_2_extend _ _ _ n); eauto. }
    (* Case 1/2 : m ∈ R *)
    * iDestruct (big_sepS_elem_of _ _ _ Hm with "HmhR") as "Hm".
      iDestruct "Hm" as (mval Hsender Hser) "Hres".
      wp_apply (s_deser_spec ((msg_serialization RCParams_srv_ser)));
        first done.
      iIntros "_".
      iDestruct "Hres" as "[Hres|(#Hsmode & [Hres|Hres])]".
      ** iDestruct "Hres" as (s2 i2 ->) "Hres". wp_pures. simpl.
         iDestruct "Hres" as "[(%Hs & #Htk) |(%Hs & #Hsmode)]"; rewrite Hs.
         (* Case A: the reply is INIT-ACK. *)
         (* Check whether the reply is INIT-ACK and #(m_sender m) = #RCParams_srv_saddr. *)
         *** case_bool_decide as Heq1; wp_pures.
             (* The reply is INIT-ACK. *)
             **** case_bool_decide as Heq2; wp_pures.
                  (* The msg is from the server *)
                  ***** iApply "HΨ". inversion Heq1.
                  iExists R0, _. iExists i2, m, _.
                  rewrite Hy1. iFrame. repeat (iSplit; first eauto).
                  by subst. eauto.
                  rewrite Hs in Hser. simpl in Hser.
                  by iDestruct ("Hcnd1" $! m i2 Hsender Hy1 Hser) as "[%Hcnd|(%Hcnd & Hck)]".
                  done.
                  ***** by rewrite Hsender in Heq2.
             (* The reply is not INIT-ACK. *)
             **** done.
         (* Case B: the reply is COOKIE-ACK. *)
         (* Check whether the reply is INIT-ACK and #(m_sender m) = #RCParams_srv_saddr. *)
         *** wp_pures.
             iApply ("IH" with  "[] [HΨ] [$Hh] [$Hmh] [$HmhR] [$Hcnd1] [$Hcnd2]"); [| ].
             { iIntros (m') "Hm'".
               iDestruct "Hm'" as (ck γs' Hser1 ? ?) "(#Htk' & Hm')".
               iApply (conn_step_1_init_holds clt_addr R0 with "[Hm']").
               iExists ck. iFrame "#∗". eauto. }
             iIntros (v) "Hpost". iApply "HΨ"; subst; eauto.
      ** iDestruct "Hres" as (ackid -> n) "(-> & Hfr)". wp_pures.
         iApply ("IH" with  "[] [HΨ] [$Hh] [$Hmh] [$HmhR] [$Hcnd1] [$Hcnd2]").
         { iIntros (m') "Hm'".
           iDestruct "Hm'" as (ck γs' Hser1 ? ?) "(#Htk & Hm')".
           iApply (conn_step_1_init_holds clt_addr R0 with "[Hm']").
           iExists ck. iFrame "#∗". eauto. }
         iIntros (v) "Hpost". iApply "HΨ"; subst; eauto.
      ** iDestruct "Hres" as (i w -> n) "(Heq & Hidmsg)". wp_pures.
         iApply ("IH" with  "[] [HΨ] [$Hh] [$Hmh] [$HmhR] [$Hcnd1] [$Hcnd2]").
         { iIntros (m') "Hm'".
           iDestruct "Hm'" as (ck γs' Hser1 ? ?) "(#Htk & Hm')".
           iApply (conn_step_1_init_holds clt_addr R0 with "[Hm']").
           iExists ck. iFrame "#∗". eauto. }
         iIntros (v) "Hpost". iApply "HΨ"; subst; eauto.
  Qed.

 End Proof_of_connect_step_1.
