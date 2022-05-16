From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants mono_nat.
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

Section Proof_of_connect_step_2.
  Context `{!anerisG Mdl Σ,
            !Reliable_communication_service_params,
            !chanG Σ,
            !lockG Σ}.
  Context `{!server_ghost_names}.

  Definition conn_step_2_init clt_addr : iProp Σ :=
   ∀ m' (n : nat),
        (⌜s_is_ser (msg_serialization RCParams_srv_ser)
         (InjLV (#"COOKIE-ACK", #n)) (m_body m')⌝ ∗
        ⌜m_sender m' = RCParams_srv_saddr⌝ ∗
        ⌜m_destination m' = clt_addr⌝ ∗
          (∃ γs : session_name,
              can_init γs (m_destination m') RCParams_protocol Left ∗
                session_connected clt_addr γs)) -∗
        client_interp m'.

  Lemma conn_step_2_init_holds clt_addr : ⊢ conn_step_2_init clt_addr.
  Proof.
    iIntros (m' n) "Hm'".
    iDestruct "Hm'" as (Hprod Hsender Hdst) "(%γs & Hcn & #Hsmode)".
    iExists (InjLV (#"COOKIE-ACK", #n)).
    iSplit; first done. iSplit; eauto. iLeft.
    iExists _, _. iSplit; first eauto.
    iExists n, γs. iSplit; first eauto.
    iDestruct "Hcn" as "(#Htk & Hcn)". iFrame "#∗".
    iRight. iSplit; first done. iExists γs. subst; iFrame; eauto.
  Qed.

  Lemma conn_step_2_server_interp_holds clt_addr s1 s (ck : nat) :
    ⌜s_is_ser (msg_serialization RCParams_clt_ser)
     (InjLV (#"COOKIE", #ck%nat)) s1⌝ ∗
    RCParams_srv_saddr ⤇ server_interp ∗
    clt_addr ⤇ client_interp ∗
    CookieRes clt_addr ck -∗
    server_interp {| m_sender := clt_addr;
                    m_destination := RCParams_srv_saddr;
                    m_protocol := sprotocol s; m_body := s1 |}.
  Proof.
    iIntros "(%Hser & #Hsrv_si & #Hclt_si & Hck)".
    iExists (InjLV (#"COOKIE", #ck%nat)). simpl.
    iFrame "Hclt_si".
    iSplit; first done.
    iLeft.
    iExists "COOKIE", "COOKIE-ACK", (Z.of_nat ck).
    iSplit; first done.
    iExists _; iSplit; first done.
    iRight.
    iDestruct "Hck" as "(%γs & #Htk & Hck)".
    do 2 (iSplit; first done).
    iSplitL "Hck"; [ iExists _; by iFrame |].
    iSplit; [iExists _; iFrame "#" | ].
    iIntros (m' n) "Hm'". iDestruct "Hm'" as (γck Hdeser Hsender Hmsg) "(#Htk' & Hcan)".
    iApply (conn_step_2_init_holds clt_addr).
    do 3 (iSplit; first done). iExists _.
    iDestruct "Hcan" as "(#Hsmode & Hcan)".
    iSplit; first subst; eauto.
  Qed.

  Definition conn_step_2_post skt h s clt_addr ck (R T : gset message) : val → iProp Σ :=
    λ (v : val),
      (∃ (m : message) (n : nat) (mt : message),
          ⌜v = #n⌝ ∗
          ⌜m ∈ R⌝ ∗
          ⌜s_is_ser (msg_serialization RCParams_srv_ser)
           (InjLV (#"COOKIE-ACK", #n)) (m_body m)⌝ ∗
          ⌜(m_destination m) = clt_addr⌝ ∗
          isClientSocketInternal skt h s clt_addr false R ({[mt]} ∪ T) ∗
          (∃ γs, can_init γs (m_destination m) RCParams_protocol Left ∗
                 session_connected clt_addr γs) ∗
          ⌜s_is_ser (msg_serialization RCParams_clt_ser) (InjLV (#"COOKIE", #ck)) (m_body mt)⌝ ∗
          ⌜(m_sender mt) = clt_addr⌝ ∗
          ⌜(m_destination mt) = RCParams_srv_saddr⌝)%I.

  Lemma client_conn_step_2_spec skt h s clt_addr R0 T0 (ck : nat) :
    {{{   isClientSocketInternal skt h s clt_addr false R0 T0 ∗
           conn_incoming_msg_cond_2 clt_addr R0 ∗
            server_init_interp clt_addr "COOKIE" "COOKIE-ACK" ck
    }}}
      client_conn_step skt (#"COOKIE", #ck)%V #"COOKIE-ACK" #RCParams_srv_saddr
      @[ip_of_address clt_addr]
      {{{  v, RET v; ∃ R1 T1, conn_step_2_post skt h s clt_addr ck R1 T1 v }}}.
  Proof.
    iIntros (Φ) "(HisClt & Hcnd2 & HresIn) HΦ".
    iDestruct "HisClt" as "(#Hsrv_si & HisClt & Hmh & #HmhR)".
    iDestruct "HisClt" as (Hskt Hsaddr Hsblock) "(Hh & #Hsi)".
    rewrite Hskt.
    iDestruct "HresIn" as "[(%Habs & _ & HresIn) | (_ & _ & Hck & HresIn)]"; first done.
    wp_lam. wp_pures.
    (* Serialize the request. *)
    wp_apply (s_ser_spec ((msg_serialization RCParams_clt_ser))).
    { eauto. iPureIntro. apply (serInit _ ck Left). }
    iIntros (s1 Hs1). wp_pures.
    (* Send it. *)
    wp_apply (aneris_wp_send _ server_interp
               with "[$Hh $Hmh Hck]"); [done|done|  | ].
    (* Prove the servers socket interp. *)
    { iSplit; iNext; first eauto.
      by iApply ((conn_step_2_server_interp_holds clt_addr s1 _ ck)
               with "[$Hsrv_si $Hsi $Hck]"). }
    iIntros "(Hh & Hmh)". wp_pures.
    set (mt :=  {|
                m_sender := clt_addr;
                m_destination := RCParams_srv_saddr;
                m_protocol := sprotocol s;
                m_body := s1
              |}).
    (* Listen. *)
    iDestruct "HresIn" as "(_ & HresIn)".
    iLöb as "IH" forall (Φ R0 T0) "HmhR Hcnd2".
    wp_apply (resend_listen_spec
                _
                (conn_step_2_init clt_addr ∗
                 conn_incoming_msg_cond_2 clt_addr R0)
                (λ (v : val),
                   ∃ (R T : gset message),
                    conn_step_2_post skt h s clt_addr ck R T v)%I
                _ _ _ _ _ mt _ client_interp
               with "[] [$Hh $Hmh $Hsi $Hcnd2]");
      [done | done | done | done |  | by iFrame "#∗"; iApply conn_step_2_init_holds | ].
    2:{ iIntros (v) "HQ".
        iDestruct "HQ" as (R T n0 m0 mt0) "(-> & %Hm0 & %Hser & %Hdst & HisClt & Hchan & %Hmt1 & %Hmt2)".
        iDestruct "HisClt" as "(#Hsrv_si2 & HisClt & Hmh2 & #HmhR2)".
        iDestruct "HisClt" as (-> Hsaddr2 Hsblock2) "(Hh2 & #Hsi2)".
        iApply ("HΦ" with "[Hh2 Hmh2 HmhR2 Hchan]"); last iFrame.
        iExists _, _. iExists n0, m0. iExists _. do 4 (iSplit; first done).
        iFrame "#∗"; eauto. }
    iIntros (m) "!#". iIntros (Ψ) "(%Hy1 & (Hy2 & Hcnd2) & Hy3) HΨ". wp_pures.
    iDestruct "Hy3" as "[(%Hm & Hh & Hmh & Hres)|(%Hm & Hh & Hmh)]".
    (* Case 1/2 : m ∉ R *)
    *  iDestruct (client_interp_le with "[$Hres]") as "#Hres_pers".
       iDestruct (big_sepS_insert_2 m with "[] [$HmhR Hres_pers]")
         as "#HmhRext"; first done.
       iDestruct "Hres" as (mval Hsender Hser) "Hres".
       wp_apply (s_deser_spec ((msg_serialization RCParams_srv_ser)));
         first done.
       iIntros "_". iDestruct "Hres" as "[Hres|(#Hsmode & [Hres|Hres])]".
       (* Case 1.1/3 : mval = InjLV (#s0, #i) *)
       ** iDestruct "Hres" as (s2 i2 ->) "Hres". wp_pures.
          iDestruct "Hres" as (n γs Hn) "(#Htk & [(%Hs & Hck )|(%Hs & Hgh)])";
            rewrite Hs; last first.
          (* Case A: the reply is COOKIE-ACK. *)
          (* Check whether the reply is COOKIE-ACK
               and #(m_sender m) = #RCParams_srv_saddr. *)
          *** subst i2. case_bool_decide as Heq1; wp_pures; last done.
              (* The reply is COOKIE-ACK. *)
              case_bool_decide as Heq2; wp_pures.
              (* The msg is from the server *)
              **** iApply "HΨ". inversion Heq1.
                   iExists _, _. iExists m, n. rewrite Hy1. iExists _.
                   iFrame "#". (iSplit; first done).
                   iSplit; first eauto with set_solver.
                   iSplit; first eauto. subst. by iPureIntro.
                   iSplit; first eauto. iFrame "Hgh". iFrame "Hmh". iFrame "Hh".
                   iPureIntro. split_and!; eauto.
              **** iApply ("IH" with  "[] [HΨ] [$Hh] [$Hmh] [$HmhRext]").
                   { iIntros (m' n') "Hm'".
                     iDestruct "Hm'" as (γs' ? ? Hdst') "(#Htk' & Hm')".
                     iApply (conn_step_2_init_holds clt_addr with "[Hm']").
                     rewrite Hdst'.
                     iDestruct "Hm'" as "(#Hsmode & Hcan)".
                     do 3 (iSplit; first done).
                     subst; eauto with iFrame. }
                   iIntros (v) "Hpost". iApply "HΨ"; subst; eauto.
                   by rewrite Hsender in Heq2.
          (* Case B: the reply is COOKIE-ACK. *)
          (* Check whether the reply is INIT-ACK and #(m_sender m) = #RCParams_srv_saddr. *)
          *** wp_pures.
              iApply ("IH" with  "[] [HΨ] [$Hh] [$Hmh] [$HmhRext]").
              { iIntros (m' n') "Hm'".
                iDestruct "Hm'" as (γs' ? ? Hdst') "(#Htk' & Hm')".
                iApply (conn_step_2_init_holds clt_addr with "[Hm']").
                rewrite Hdst'.
                iDestruct "Hm'" as "(#Hsmode & Hcan)".
                do 3 (iSplit; first done).
                subst; eauto with iFrame. }
              iIntros (v) "Hpost". iApply "HΨ"; subst; eauto.
              subst.
              iApply (conn_incoming_msg_cond_2_extend with "[] [$Hcnd2]"); eauto.
       ** iDestruct "Hres" as (ackid -> n) "(-> & #Hfr)". wp_pures.
          iApply ("IH" with  "[] [HΨ] [$Hh] [$Hmh] [$HmhRext]").
          iDestruct "Hfr" as (γs') "(#Htk & _)".
          { iIntros (m' n') "Hm'".
            iDestruct "Hm'" as (γ ? Hser1 Hdst') "(#Htk' & Hm')".
            iApply (conn_step_2_init_holds clt_addr with "[Hm']").
            rewrite Hdst'.
            do 3 (iSplit; first done).
            iDestruct "Hm'" as "(#Hsmode' & Hcan)".
            subst; eauto with iFrame. }
          iIntros (v) "Hpost". iApply "HΨ"; subst; eauto.
          iApply (conn_incoming_msg_cond_2_extend _ _ _ n with "[] [$Hcnd2]"); eauto.
       ** iDestruct "Hres" as (i w -> n) "(Heq & #Hidmsg)". wp_pures.
          iApply ("IH" with  "[] [HΨ] [$Hh] [$Hmh] [$HmhRext]").
          iDestruct "Hidmsg" as (γs') "(#Htk & _)".
          { iIntros (m' n') "Hm'".
            iDestruct "Hm'" as (γ ? Hser1 Hdst') "(#Htk' & Hm')".
            iApply (conn_step_2_init_holds clt_addr with "[Hm']").
            rewrite Hdst';
            iDestruct "Hm'" as "(#Hsmode' & Hcan)".
            do 3 (iSplit; first done).
            subst; eauto with iFrame. }
          iIntros (v) "Hpost". iApply "HΨ"; subst; eauto.
          iApply (conn_incoming_msg_cond_2_extend _ _ _ n with "[] [$Hcnd2]"); eauto.
     (* Case 1/2 : m ∈ R *)
    * iDestruct (big_sepS_elem_of _ _ _ Hm with "[$HmhR]") as "#Hm".
      iDestruct "Hm" as (mval Hsender Hser) "#Hres".
      wp_apply (s_deser_spec ((msg_serialization RCParams_srv_ser)));
        first done.
      iIntros "_".
      iDestruct "Hres" as "[#Hres|(#Hsmode & [#Hres|#Hres])]".
      ** iDestruct "Hres" as (s2 i2 ->) "#Hres". wp_pures. simpl.
         iDestruct "Hres" as "[(%Hs & #Htk)|(%Hs & #Hsmode')]"; rewrite Hs.
         (* Case A: the reply is INIT-ACK. *)
         (* Check whether the reply is INIT-ACK and #(m_sender m) = #RCParams_srv_saddr. *)
         *** case_bool_decide as Heq1; wp_pures. done.
             (* The reply is INIT-ACK. *)
             **** iApply ("IH" with  "[] [HΨ] [$Hh] [$Hmh] [$HmhR]").
                  { iIntros (m' n') "Hm'".
                    iDestruct "Hm'" as (γs' ? ? Hdst') "(#Htk' & Hm')".
                    iApply (conn_step_2_init_holds clt_addr with "[Hm']").
                    rewrite Hdst';
                      iDestruct "Hm'" as "(#Hsmode' & Hcan)".
                    do 3 (iSplit; first done).
                    subst; eauto with iFrame. }
                  iIntros (v) "Hpost". iApply "HΨ"; subst; eauto.
                  subst; eauto.
         (* Case B: the reply is COOKIE-ACK. *)
         (* Check whether the reply is INIT-ACK and #(m_sender m) = #RCParams_srv_saddr. *)
         *** case_bool_decide as Heq1; wp_pures.
             **** case_bool_decide as Heq2; wp_pures.
                  (* The msg is from the server *)
                  ***** iApply "HΨ".
                  iExists R0, _. iExists m, i2.
                  rewrite Hy1. iExists _. iFrame.
                  repeat (iSplit; first eauto). by subst. done.
                  rewrite Hs in Hser. simpl in Hser.
                  iDestruct "Hsmode'" as (γs') "#Hsmode'".
                  iDestruct ("Hcnd2" $! m i2 Hsender Hy1 Hser) as "[%Hcnd|(%Hcnd & (%γs0 & Hinit))]"; first done.
                  iAssert (⌜γs0 = γs'⌝)%I as "%Heq".
                  { iDestruct "Hinit" as "(#Htk1 & _)".
                    iDestruct "Hsmode'" as "(#Htk2 & _)".
                    by iApply session_token_agree. }
                  rewrite Heq.
                  iExists γs'. eauto. done.
                  ***** rewrite Hsender in Heq2. done.
             **** done.
      ** iDestruct "Hres" as (ackid -> n) "(-> & (%γs & #Htk & Hfr))". wp_pures.
         iApply ("IH" with  "[] [HΨ] [$Hh] [$Hmh] [$HmhR] [$Hcnd2]").
         { iIntros (m' n') "Hm'".
           iDestruct "Hm'" as (γ ? Hser1 Heq2) "(#Htk' & Hm')".
           rewrite -Heq2.
           iApply (conn_step_2_init_holds clt_addr with "[Hm']").
           rewrite Heq2.
           iDestruct "Hm'" as "(#Hsmode' & Hcan)".
           do 3 (iSplit; first done).
           subst; eauto with iFrame. }
         iIntros (v) "Hpost". iApply "HΨ"; subst; eauto.
      ** iDestruct "Hres" as (i w -> n) "(Heq & (%γs & #Htk & Hfr))". wp_pures.
         iApply ("IH" with  "[] [HΨ] [$Hh] [$Hmh] [$HmhR] [$Hcnd2]").
         { iIntros (m' n') "Hm'".
           iDestruct "Hm'" as (γ ? Hser1 Heq2) "(#Htk' & Hm')".
           rewrite -Heq2.
           iApply (conn_step_2_init_holds clt_addr with "[Hm']").
            iDestruct "Hm'" as "(#Hsmode' & Hcan)".
            do 3 (iSplit; first done).
            iExists γ.
            rewrite Heq2.
            subst; eauto with iFrame. }
         iIntros (v) "Hpost". iApply "HΨ"; subst; eauto.
         Unshelve. apply _. apply _.
  Qed.

End Proof_of_connect_step_2.
