From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang Require Import tactics proofmode.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre aneris_lifting.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import lock_proof.
From actris.channel Require Export proto.
From aneris.examples.reliable_communication
     Require Import client_server_code user_params.
From aneris.examples.reliable_communication.spec
     Require Import resources api_spec proofmode ras.
From aneris.examples.reliable_communication.examples.hello_world_2
     Require Import hello_world_2_code.

(* -------------------------------------------------------------------------- *)
(** The communication protocol. *)
(* -------------------------------------------------------------------------- *)
Section Proto.
  Context `{!anerisG Mdl Σ}.

  Definition proto_hello_world : iProto Σ :=
    (<! (s : string) > MSG #s ; <?> MSG #s; END)%proto.

End Proto.


(* -------------------------------------------------------------------------- *)
(** The proof of the code assuming resources. *)
(* -------------------------------------------------------------------------- *)
Section proof_of_the_client_code.
  Context `{!anerisG Mdl Σ, !lockG Σ, !SpecChanG Σ}.
  Context
    (srv_sa0 : socket_address)
    (srv_sa1 : socket_address)
    (A : gset socket_address)
    (Hneq : srv_sa0 ≠ srv_sa1)
    (N1 N2 : namespace).

  (* TODO: maybe use record mechanism instead of TC for user params. *)
  Global Instance up0
    : Reliable_communication_service_params :=
  {| RCParams_clt_ser := string_serialization;
    RCParams_srv_ser := string_serialization;
    RCParams_srv_ser_inj := ser_inj.string_ser_is_ser_injective;
    RCParams_srv_ser_inj_alt := ser_inj.string_ser_is_ser_injective_alt;
    RCParams_clt_ser_inj := ser_inj.string_ser_is_ser_injective;
    RCParams_clt_ser_inj_alt := ser_inj.string_ser_is_ser_injective_alt;
    RCParams_srv_saddr := srv_sa0;
    RCParams_protocol := proto_hello_world;
    RCParams_srv_N := N1
  |}.

  Global Instance up1
    : Reliable_communication_service_params :=
  {| RCParams_clt_ser := string_serialization;
    RCParams_srv_ser := string_serialization;
    RCParams_srv_ser_inj := ser_inj.string_ser_is_ser_injective;
    RCParams_srv_ser_inj_alt := ser_inj.string_ser_is_ser_injective_alt;
    RCParams_clt_ser_inj := ser_inj.string_ser_is_ser_injective;
    RCParams_clt_ser_inj_alt := ser_inj.string_ser_is_ser_injective_alt;
    RCParams_srv_saddr := srv_sa1;
    RCParams_protocol := proto_hello_world;
    RCParams_srv_N := N2
  |}.

  Context (chn0 : @Chan_mapsto_resource Σ).
  Context (SnRes0 : SessionResources up0).
  Context (HspecsS0 : Reliable_communication_Specified_API_session chn0).
  Context (HspecsN0 : @Reliable_communication_Specified_API_network _ _ _ chn0 up0 SnRes0).
  Context (chn1 : @Chan_mapsto_resource Σ).
  Context (SnRes1 : SessionResources up1).
  Context (HspecsS1 : Reliable_communication_Specified_API_session chn1).
  Context (HspecsN1 : @Reliable_communication_Specified_API_network _ _ _ chn1 up1 SnRes1).

  Lemma wp_client clt_addr0 clt_addr1 :
    {{{ up0.(RCParams_srv_saddr) ⤇ @reserved_server_socket_interp _ _ _ up0 SnRes0 ∗
        up1.(RCParams_srv_saddr) ⤇ @reserved_server_socket_interp _ _ _ up1 SnRes1 ∗
        ⌜ip_of_address clt_addr0 = ip_of_address clt_addr1⌝ ∗
        clt_addr0 ⤳ (∅, ∅) ∗
        free_ports (ip_of_address clt_addr0)
                   {[port_of_address clt_addr0]} ∗
        unallocated {[clt_addr0]} ∗
        clt_addr1 ⤳ (∅, ∅) ∗
        free_ports (ip_of_address clt_addr1)
                   {[port_of_address clt_addr1]} ∗
        unallocated {[clt_addr1]} }}}
       client #clt_addr0 #clt_addr1 #srv_sa0 #srv_sa1 @[ip_of_address clt_addr0]
    {{{ skt, RET skt; True }}}.
  Proof.
    iIntros (Φ) "(#Hsi0 & #Hsi1 & %Heq & Hmh0 & Hfp0 & Hf0 & Hmh1 & Hfp1 & Hf1) HΦ".
    rewrite /client.
    wp_lam.
    wp_pures.
    destruct HspecsN0 as [Hcl0 Hsrv0 Hcnt0 Hlst0 Hac0].
    destruct HspecsN1 as [Hcl1 Hsrv1 Hcnt1 Hlst1 Hac1].
    wp_apply (Hcl0 with "[$Hmh0 $Hfp0 $Hsi0 $Hf0][Hfp1 Hmh1 Hf1 HΦ]").
    iNext. iIntros (skt0) "Hcl0".
    wp_pures.
    rewrite Heq.
    wp_apply (Hcl1 clt_addr1 with "[$Hmh1 $Hfp1 $Hsi1 $Hf1][HΦ Hcl0]").
    iNext. iIntros (skt1) "Hcl1".
    wp_pures.
    rewrite -Heq.
    wp_apply (Hcnt0 with "[$Hcl0][HΦ Hcl1]").
    iNext.
    iIntros (c0) "Hc0".
    wp_pures.
    rewrite Heq.
    wp_apply (Hcnt1 with "[$Hcl1][HΦ Hc0]").
    iNext.
    iIntros (c1) "Hc1".
    wp_pures.
    wp_send_chan chn0 with "[//]".
    wp_pures.
    wp_send_chan chn1 with "[//]".
    by iApply "HΦ".
  Qed.

End proof_of_the_client_code.

Section proof_of_the_server_code.
  Context `{!anerisG Mdl Σ, !lockG Σ, !SpecChanG Σ}.
  Context
    (srv_sa : socket_address)
    (A : gset socket_address)
    (p : iProto Σ)
    (N : namespace).

  (* TODO: maybe use record mechanism instead of TC for user params. *)
  Global Instance hw_rcsparams
    : Reliable_communication_service_params :=
  {| RCParams_clt_ser := string_serialization;
    RCParams_srv_ser := string_serialization;
    RCParams_srv_ser_inj := ser_inj.string_ser_is_ser_injective;
    RCParams_srv_ser_inj_alt := ser_inj.string_ser_is_ser_injective_alt;
    RCParams_clt_ser_inj := ser_inj.string_ser_is_ser_injective;
    RCParams_clt_ser_inj_alt := ser_inj.string_ser_is_ser_injective_alt;
    RCParams_srv_saddr := srv_sa;
    RCParams_protocol := proto_hello_world;
    RCParams_srv_N := N
  |}.

  Context (SnRes : SessionResources hw_rcsparams).
  Context `{!Reliable_communication_Specified_API_session chn}.
  Context `{!Reliable_communication_Specified_API_network hw_rcsparams SnRes}.

 Lemma wp_server :
    {{{ RCParams_srv_saddr ⤇ reserved_server_socket_interp ∗
          RCParams_srv_saddr ⤳ (∅, ∅) ∗
        free_ports (ip_of_address RCParams_srv_saddr)
                   {[port_of_address RCParams_srv_saddr]} ∗
        SrvInit }}}
       server #RCParams_srv_saddr @[ip_of_address RCParams_srv_saddr]
    {{{ skt, RET skt; True }}}.
  Proof.
    iIntros (Φ) "(#Hsi & Hmh & Hfp & Hit) HΦ".
    rewrite /server.
    wp_lam.
    wp_apply (RCSpec_make_server_skt_spec
               with "[$Hmh $Hfp $Hsi $Hit][HΦ]").
    iNext. iIntros (skt) "Hcl".
    wp_pures.
    wp_apply (RCSpec_server_listen_spec with "[$Hcl][HΦ]").
    iNext. iIntros "Hp".
    wp_pures.
    wp_apply (RCSpec_accept_spec with "[$Hp][HΦ]").
    iNext. iIntros (c caddr) "(Hlst & Hc)".
    wp_pures.
    simpl in *.
    rewrite /proto_hello_world.
    wp_pures. wp_recv (x) as "_".
    wp_pures.
    wp_send with "[//]".
    iApply "HΦ". eauto with iFrame.
  Qed.

End proof_of_the_server_code.

(* -------------------------------------------------------------------------- *)
(** The proof of the runner (main) that spawns all machines used in the code. *)
(* -------------------------------------------------------------------------- *)

From aneris.examples.reliable_communication.instantiation
     Require Import instantiation_of_init.

(** Concrete parameters (addresses, ips) *)
Definition srv_sa0 := SocketAddressInet "0.0.0.0" 80.
Definition srv_sa1 := SocketAddressInet "0.0.0.1" 80.
Definition clt_sa80 := SocketAddressInet "0.0.0.2" 80.
Definition clt_sa81 := SocketAddressInet "0.0.0.2" 81.

Definition A : gset socket_address := {[ srv_sa0; srv_sa1 ]}.
Definition ips : gset string := {[ "0.0.0.0" ; "0.0.0.1"; "0.0.0.2" ]}.
Lemma inA0 : srv_sa0 ∈ A. Proof. set_solver. Qed.
Lemma inA1 : srv_sa1 ∈ A. Proof. set_solver. Qed.

Definition main : expr :=
    Start "0.0.0.0" (server #srv_sa0) ;;
    Start "0.0.0.1" (server #srv_sa1) ;;
    Start "0.0.0.2" (client #clt_sa80 #clt_sa81 #srv_sa0 #srv_sa1).

Section proof_of_the_main.
  Context `{!anerisG Mdl Σ, !SpecChanG Σ}.

  (** Concrete instances of the User Parameters. *)
  Definition UP0 := hw_rcsparams srv_sa0 (nroot .@ "hw0").
  Definition UP1 := hw_rcsparams srv_sa1 (nroot .@ "hw1").

  Context  (chn0 : @Chan_mapsto_resource Σ).
  Context  (chn1 : @Chan_mapsto_resource Σ).
  Context  (HsAPIs0 : @Reliable_communication_Specified_API_session _ _ _ chn0).
  Context  (HsAPIs1 : @Reliable_communication_Specified_API_session _ _ _ chn1).
  Context  (SnRes0 : SessionResources UP0).
  Context  (SnRes1 : SessionResources UP1).
  Context  (HsAPIn0 : @Reliable_communication_Specified_API_network _ _ _ chn0 UP0 SnRes0).
  Context  (HsAPIn1 : @Reliable_communication_Specified_API_network _ _ _ chn1 UP1 SnRes1).

  Lemma main_spec :
    ⊢ |={⊤}=>
         srv_sa0 ⤇ @reserved_server_socket_interp _ _ _ UP0 SnRes0 -∗
         srv_sa1 ⤇ @reserved_server_socket_interp _ _ _ UP1 SnRes1 -∗
         unallocated {[clt_sa80; clt_sa81]} -∗
         free_ip "0.0.0.0" -∗
         free_ip "0.0.0.1" -∗
         free_ip "0.0.0.2" -∗
         SocketAddressInet "0.0.0.0" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.1" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.2" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.2" 81 ⤳ (∅, ∅) -∗
         @SrvInit _ _ _ UP0 SnRes0 -∗
         @SrvInit _ _ _ UP1 SnRes1 -∗
         WP main @["system"]
      {{ v, True }}.
  Proof.
    destruct HsAPIn0, HsAPIs0.
    destruct HsAPIn1, HsAPIs1.
    iIntros "".
    iModIntro.
    iIntros "#Hsrv0 #Hsrv1 Hf Hfree0 Hfree1 Hfree2 Hsa0 Hsa1 Hsa2 Hsa3 HSrvInit0 HSrvInit1".
    rewrite /main.
    (* Server 1. *)
    wp_apply aneris_wp_start; first done.
    iFrame "Hfree0".
    iSplitR "Hsa0 HSrvInit0"; last first.
    { iNext. iIntros "Hfps".
      iApply (@wp_server _ _ _ _ _ _ SnRes0 chn0 _ with "[-]"); last done. by iFrame "#∗". }
    iNext. wp_pures.
    (* Server 2. *)
    wp_apply aneris_wp_start; first done.
    iFrame "Hfree1".
    iSplitR "Hsa1 HSrvInit1"; last first.
    { iNext. iIntros "Hfps".
      iApply (@wp_server _ _ _ _ _ _ SnRes1 chn1 _ with "[-]"); last done. by iFrame "#∗". }
    iNext. wp_pures.
    wp_apply (aneris_wp_start {[80%positive; 81%positive]}); first done.
    iFrame "Hfree2".
    iSplit; first done.
    iNext. iIntros "Hfps".
    iDestruct (unallocated_split with "Hf") as "[Hf0 Hf1]"; [set_solver|].
    iApply (wp_client srv_sa0 srv_sa1 _ _ chn0 SnRes0 _ _ chn1 SnRes1 _ _ clt_sa80 clt_sa81
             with "[Hsa2 Hsa3 Hfps Hf0 Hf1]"); last done.
    iSplit; first done. iFrame "#∗".
    iSplit; first done.
    iPoseProof (free_ports_split "0.0.0.2" {[80%positive]} {[81%positive]})  as "(Hlm1 & _)"; first by set_solver.
    iDestruct ("Hlm1" with "[$Hfps]") as "(Hf1 & Hf2)".
    iFrame; eauto.    
  Qed.

End proof_of_the_main.


(* -------------------------------------------------------------------------- *)
(** The proof of adequacy (the program does not crash). *)
(* -------------------------------------------------------------------------- *)

Definition init_state :=
  {|
    state_heaps := {[ "system" := ∅ ]};
    state_sockets := {[ "system" := ∅ ]};
    state_ports_in_use :=
      <["0.0.0.0" := ∅ ]> $ <["0.0.0.1" := ∅ ]> $  <["0.0.0.2" := ∅ ]> $ ∅;
    state_ms := ∅;
  |}.

From aneris.examples.reliable_communication.resources
     Require Import prelude socket_interp.
From aneris.examples.reliable_communication.spec
     Require Import ras resources.

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

Theorem adequacy : aneris_adequate main "system" init_state (λ _, True).
Proof.
  set (Σ := #[anerisΣ dummy_model; SpecChanΣ]).
  eapply (@adequacy Σ dummy_model _ _ ips {[clt_sa80; clt_sa81; srv_sa0; srv_sa1]} ∅ ∅ ∅);
    try set_solver; last first.
  2:{ apply dummy_model_finitary . }
  iIntros (Hdg) "".
  iMod (Reliable_communication_init_instance ⊤ UP0)
    as (chn0 sgn0 SnRes0) "(HsrvInit0 & Hspecs0)"; [ solve_ndisj|].
  iDestruct "Hspecs0"
    as "(
           %HmkClt0 & %HmkSrv0
         & %Hconnect0
         & %Hlisten0 & %Haccept0
         & %Hsend0 & %HsendTele0
         & %HtryRecv0 & %Hrecv0)".
  iMod (Reliable_communication_init_instance ⊤ UP1)
    as (chn1 sgn1 SnRes1) "(HsrvInit1 & Hspecs1)"; [ solve_ndisj|].
  iDestruct "Hspecs1"
    as "(
           %HmkClt1 & %HmkSrv1
         & %Hconnect1
         & %Hlisten1 & %Haccept1
         & %Hsend1 & %HsendTele1
         & %HtryRecv1 & %Hrecv1)".
  iMod (@main_spec _ _ _ _ chn0 chn1) as "Hmain".
  split; try done.
  split; try done.
  instantiate (1 := SnRes0).
  split; try done.
  instantiate (1 := SnRes1).
  split; try done.
  iModIntro.
  iIntros "Hf Hb Hfg Hips _ _ _ _ _".
  simpl in *.
  iDestruct (unallocated_split with "Hf") as "[Hf Hf1]"; [set_solver|].
  iDestruct (unallocated_split with "Hf") as "[Hf Hf0]"; [set_solver|].
  iApply (aneris_wp_socket_interp_alloc_singleton
            (@reserved_server_socket_interp _ _ _ UP0 SnRes0) with "Hf0").
  iIntros "Hsi0".
  iApply (aneris_wp_socket_interp_alloc_singleton
            (@reserved_server_socket_interp _ _ _ UP1 SnRes1) with "Hf1").
  iIntros "Hsi1".
  iDestruct (big_sepS_delete _ _ "0.0.0.0" with "Hips") as "[Hip0 Hips]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "0.0.0.1" with "Hips") as "[Hip1 Hips]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "0.0.0.2" with "Hips") as "[Hip2 Hips]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ srv_sa0 with "Hb") as "[Hm0 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ srv_sa1 with "Hms") as "[Hm1 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ clt_sa80 with "Hms") as "[Hc0 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ clt_sa81 with "Hms") as "[Hc1 _]";
    first set_solver.
  iApply ("Hmain" with "[$Hsi0][$Hsi1][$Hf][$Hip0][$Hip1][$Hip2][$Hm0][$Hm1][$Hc0][$Hc1][$HsrvInit0][$HsrvInit1]").
Qed.
