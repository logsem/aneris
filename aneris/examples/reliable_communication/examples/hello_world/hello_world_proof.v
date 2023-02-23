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
From aneris.examples.reliable_communication.examples.hello_world
     Require Import hello_world_code.

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
Section proof_of_the_code.
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
    wp_apply (RCSpec_make_server_skt_spec with "[$Hmh $Hfp $Hsi $Hit][HΦ]").
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

  Lemma wp_client clt_addr :
    {{{ RCParams_srv_saddr ⤇ reserved_server_socket_interp ∗
        clt_addr ⤳ (∅, ∅) ∗
        free_ports (ip_of_address clt_addr)
                   {[port_of_address clt_addr]} ∗
        unallocated {[clt_addr]} }}}
       client #clt_addr #srv_sa @[ip_of_address clt_addr]
    {{{ skt, RET skt; True }}}.
  Proof.
    iIntros (Φ) "(#Hsi & Hmh & Hfp & Hf) HΦ".
    rewrite /client.
    wp_lam.
    wp_pures.
    wp_apply (RCSpec_make_client_skt_spec with "[$Hmh $Hfp $Hsi $Hf][HΦ]").
    iNext. iIntros (skt) "Hcl".
    wp_pures.
    wp_apply (RCSpec_connect_spec with "[$Hcl][HΦ]").
    iNext.
    iIntros (c) "Hc".
    wp_pures.
    simpl in *.
    rewrite /proto_hello_world.
    wp_send with "[//]".
    iApply "HΦ". eauto with iFrame.
  Qed.

End proof_of_the_code.


(* -------------------------------------------------------------------------- *)
(** The proof of the runner (main) that spawns all machines used in the code. *)
(* -------------------------------------------------------------------------- *)

From aneris.examples.reliable_communication.instantiation
     Require Import instantiation_of_init.

(** Concrete parameters (addresses, ips) *)
Definition srv_sa := SocketAddressInet "0.0.0.0" 80.
Definition clt_sa := SocketAddressInet "0.0.0.1" 80.
Definition ips : gset string := {[ "0.0.0.0" ; "0.0.0.1"]}.

Definition main : expr :=
    Start "0.0.0.0" (server #srv_sa) ;;
    Start "0.0.0.1" (client #clt_sa #srv_sa).

Section proof_of_the_main.
  Context `{!anerisG Mdl Σ, !SpecChanG Σ}.

  (** Concrete instance of the User Parameters. *)
  Definition UP := hw_rcsparams srv_sa (nroot .@ "hw").

  Context `{chn : @Chan_mapsto_resource Σ}.
  Context  (SnRes : SessionResources UP).
  Context  (HsAPIn : Reliable_communication_Specified_API_network UP SnRes).
  Context  (HsAPIs : Reliable_communication_Specified_API_session _).
  Lemma main_spec :
    ⊢ |={⊤}=>
         srv_sa ⤇ @reserved_server_socket_interp _ _ _ UP SnRes -∗
         unallocated {[clt_sa]} -∗
         free_ip "0.0.0.0" -∗
         free_ip "0.0.0.1" -∗
         SocketAddressInet "0.0.0.0" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.1" 80 ⤳ (∅, ∅) -∗
         @SrvInit _ _ _ UP SnRes -∗
         WP main @["system"]
      {{ v, True }}.
  Proof.
    destruct HsAPIn, HsAPIs.
    iIntros "".
    iModIntro.
    iIntros "#Hsrv Hf Hfree1 Hfree2 Hsa1 Hsa2 HSrvInit".
    rewrite /main.
    wp_apply aneris_wp_start.
    iFrame "Hfree1".
    iSplitR "Hsa1 HSrvInit"; last first.
    { iNext. iIntros "Hfps".
      iApply (@wp_server _ _ _ _ _ _ SnRes chn _ with "[-]"); last done.
      by iFrame "#∗". }
    iNext. wp_pures.
    wp_apply aneris_wp_start.
    iFrame "Hfree2".
    iSplit; first done.
    iNext. iIntros "Hfps".
    iApply (@wp_client _ _ _ _ _ _ SnRes chn _ _ clt_sa with "[-]");
      last done.
    by iFrame "#∗".
  Qed.

End proof_of_the_main.


(* -------------------------------------------------------------------------- *)
(** The proof of adequacy (the program does not crash). *)
(* -------------------------------------------------------------------------- *)

Definition init_state :=
  {|
    state_heaps := {[ "system" := ∅ ]};
    state_sockets := {[ "system" := ∅ ]};
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
  eapply (@adequacy Σ dummy_model _ _ ips {[clt_sa; srv_sa]} ∅ ∅ ∅);
    try set_solver; last first.
  2:{ apply dummy_model_finitary . }
  iIntros (Hdg) "".
  iMod (Reliable_communication_init_instance ⊤ UP)
    as (chn sgn SnRes) "(HsrvInit & Hspecs)"; [ solve_ndisj|].
  iDestruct "Hspecs"
    as "(
           %HmkClt & %HmkSrv
         & %Hconnect
         & %Hlisten & %Haccept
         & %Hsend & %HsendTele
         & %HtryRecv & %Hrecv)".
  iMod (main_spec) as "Hmain".
  split; try done.
  split; try done.
  iModIntro.
  iIntros "Hf Hb Hfg Hips _ _ _ _ _".
  simpl in *.
  iDestruct (unallocated_split with "Hf") as "[Hf Hf_srv]"; [set_solver|].
  iApply (aneris_wp_socket_interp_alloc_singleton
            (@reserved_server_socket_interp _ _ _ UP SnRes) with "Hf_srv").
  iIntros "Hsi".
  iDestruct (big_sepS_delete _ _ "0.0.0.0" with "Hips") as "[Hip0 Hips]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "0.0.0.1" with "Hips") as "[Hip1 _]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ srv_sa with "Hb") as "[Hm0 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ clt_sa with "Hms") as "[Hm1 _]";
    first set_solver.
  iApply ("Hmain" with "[$Hsi][$Hf][$Hip0][$Hip1][$Hm0][$Hm1][$HsrvInit]").
Qed.
