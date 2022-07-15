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
        ⌜RCParams_srv_saddr ∈ A⌝ ∗
        fixed A ∗
        SrvInit }}}
       server #RCParams_srv_saddr @[ip_of_address RCParams_srv_saddr]
    {{{ skt, RET skt; True }}}.
  Proof.
    iIntros (Φ) "(#Hsi & Hmh & Hfp & Hf & Hit) HΦ".
    rewrite /server.
    wp_lam.
    wp_apply (RCSpec_make_server_skt_spec with "[$Hmh $Hfp $Hf $Hsi $Hit][HΦ]").
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
        ⌜clt_addr ∉ A⌝ ∗
        clt_addr ⤳ (∅, ∅) ∗
        free_ports (ip_of_address clt_addr)
                   {[port_of_address clt_addr]} ∗
        fixed A }}}
       client #clt_addr #srv_sa @[ip_of_address clt_addr]
    {{{ skt, RET skt; True }}}.
  Proof.
    iIntros (Φ) "(#Hsi & #Hca & Hmh & Hfp & Hf) HΦ".
    rewrite /client.
    wp_lam.
    wp_pures.
    wp_apply (RCSpec_make_client_skt_spec with "[$Hmh $Hfp $Hca $Hsi $Hf][HΦ]").
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
Definition A : gset socket_address := {[ srv_sa ]}.
Definition ips : gset string := {[ "0.0.0.0" ; "0.0.0.1"]}.
Lemma inA : srv_sa ∈ A. Proof. set_solver. Qed.

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
         fixed A -∗
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
    iIntros "#Hsrv #Hfixed Hfree1 Hfree2 Hsa1 Hsa2 HSrvInit".
    rewrite /main.
    wp_apply aneris_wp_start; first done.
    iFrame "Hfree1".
    iSplitR "Hsa1 HSrvInit"; last first.
    { iNext. iIntros "Hfps".
      iApply (@wp_server _ _ _ _ _ A _ SnRes chn _ with "[-]"); last done.
      by iFrame "#∗". }
    iNext. wp_pures.
    wp_apply aneris_wp_start; first done.
    iFrame "Hfree2".
    iSplit; first done.
    iNext. iIntros "Hfps".
    iApply (@wp_client _ _ _ _ _ A _ SnRes chn _ _ clt_sa with "[-]");
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
    state_ports_in_use :=
      <["0.0.0.0" := ∅ ]> $ <["0.0.0.1" := ∅ ]> $ ∅;
    state_ms := ∅;
  |}.

From aneris.examples.reliable_communication.resources
     Require Import prelude socket_interp.
From aneris.examples.reliable_communication.spec
     Require Import ras resources.

Definition fixed_dom : gset socket_address := {[ srv_sa ]}.

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
Definition socket_interp
           `{ag: !anerisG empty_model Σ}
           `{!SpecChanG Σ}
           `{server_ghost_names}
            (HinA : srv_sa ∈ fixed_dom)
            (N : namespace)
            (SnRes : SessionResources UP) sa : socket_interp Σ :=
  (match sa with
   | SocketAddressInet "0.0.0.0" 80 =>  @reserved_server_socket_interp _ _ ag UP SnRes
 (* @server_interp _ _ ag _ _ UP *)

   | _ => λ msg, ⌜True⌝
   end)%I.

Theorem adequacy : aneris_adequate main "system" init_state (λ _, True).
Proof.
  set (Σ := #[anerisΣ dummy_model; SpecChanΣ]).
  eapply (@adequacy Σ dummy_model _ _ ips fixed_dom {[srv_sa; clt_sa]} ∅ ∅ ∅);
    try done; last first.
  { set_solver. }
  { intros i. rewrite /ips !elem_of_union !elem_of_singleton.
    intros [|]; subst; simpl; set_solver. }
  { rewrite /ips /= !dom_insert_L dom_empty_L right_id_L //. }
  iIntros (Hdg) "".
  2:{ apply dummy_model_finitary . }
  iMod (Reliable_communication_init_instance ⊤ UP)
    as (chn sgn SnRes) "(HsrvInit & Hspecs)"; [ solve_ndisj|].
  iDestruct "Hspecs"
    as "(
           %HmkClt & %HmkSrv
         & %Hconnect
         & %Hlisten & %Haccept
         & %Hsend & %HsendTele
         & %HtryRecv & %Hrecv)".
  iExists (socket_interp inA (nroot .@ "hw") SnRes).
  iMod (main_spec) as "Hmain".
  split; try done.
  split; try done.
  iModIntro.
  iIntros "Hf Hsi Hb Hfg Hips _ _ _ _ _".
  simpl in *.
  iDestruct (big_sepS_delete _ _ srv_sa with "Hsi") as "[Hsi _]";
    first set_solver.
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
