From aneris.aneris_lang Require Import tactics proofmode adequacy.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre aneris_adequacy.
From aneris.aneris_lang.lib Require Import network_util_code network_util_proof.
From aneris.aneris_lang Require Import no_model.
Set Default Proof Using "Type".

Definition pong : val :=
  λ: "addr",
  let: "socket" := NewSocket #() in
  SocketBind "socket" "addr";;
  (* sockets are per default in blocking mode when allocated so we are
     guaranteed to receive a message *)
  let: "m" := unSOME (ReceiveFrom "socket") in
  let: "msg" := Fst "m" in
  let: "sender" := Snd "m" in
  (if: "msg" = #"PING" then SendTo "socket" #"PONG" "sender"
   else assert #false).

Definition ping : val :=
  λ: "addr" "server",
  let: "socket" := NewSocket #() in
  SocketBind "socket" "addr";;
  SendTo "socket" #"PING" "server";;
  Fst (unSOME (ReceiveFrom "socket")).

(** The specification for the [pong] server  *)
Section pong.
  Context `{dG : anerisG Σ}.

  (** A socket protocol is a predicate on messages and facilitates
      rely-guarantee style reasoning.

      When sending a message [m] to an address [a], the sender is obligated to prove
      [Φ m] if [a] is governed by the protocol [Φ]. In turn, when receiving a
      message [m], the receiver obtains the resources [Φ m]. *)
  Definition pong_protocol : socket_interp Σ  :=
    λ (m : message),
     (* the sender is governed by a protocol and the message body is 'PING' *)
     (∃ ϕ, m_sender m ⤇ ϕ ∗ ⌜m_body m = "PING"⌝
          (* the sender's protocol is satisfied with a 'PONG' response *)
          ∗ (<pers> ∀ m', ⌜m_body m' = "PONG"⌝ → ϕ m'))%I.

  Lemma pong_spec a ip port :
    ip = ip_of_address a →
    port = port_of_address a →
    {{{ (* the address [a] is governed by [pong_protocol] *)
        a ⤇ pong_protocol ∗
        (* the socket address [a] is free  *)
        free_ports ip {[port]} ∗
        (* exclusive ownership of the history of sent and received messages on [a] *)
        a ⤳ (∅, ∅) }}}
      pong #a @[ip] {{{ RET #(String.length "PONG"); True }}}.
  Proof.
    iIntros (-> -> Φ) "(#Hpong & Hp & Ha) HΦ".
    wp_lam.
    wp_socket h as "Hh".
    wp_let.
    wp_socketbind.
    wp_apply (aneris_wp_receivefrom with "[$Hpong $Hh $Ha]"); [done|done|done|].
    (* Either we received a fresh message or a duplicate  *)
    iIntros (m) "[% [(_ & Hh & Ha & _ & Hm) | (% & Hh & Ha)]]".
    2: { (* Since no messages have been received yet, a duplicate is not possible
         and we get a contradiction *)
         done. }
    iDestruct "Hm" as (Ψ) "(#HΨ & -> & #Hresp)".
    wp_apply wp_unSOME; [done|].
    iIntros "_".
    wp_let.
    wp_proj.
    wp_let.
    wp_proj.
    wp_let.
    wp_op.
    wp_if_true.
    wp_apply (aneris_wp_send with "[$Hh $Ha $HΨ]"); [done|done| | ].
    { iApply "Hresp". iModIntro. simpl. done. }
    iIntros "[Hh Ha]".
    by iApply "HΦ".
  Qed.

End pong.

(** The specification for the [ping] client  *)
Section ping.
  Context `{dG : anerisG Σ}.

  Definition ping_protocol : socket_interp Σ :=
    (* We're satisfied with just a 'PONG' response  *)
    (λ msg, ⌜m_body msg = "PONG"⌝)%I.

  Lemma ping_spec a b ip port :
    ip = ip_of_address a →
    port = port_of_address a →
    {{{ (* the [b] address is governed by [pong_sprotocol] *)
        b ⤇ pong_protocol
        (* the socket protocol has not yet been allocated for the address [a] *)
        ∗ unallocated {[a]}
        (* the socket address [a] is free *)
        ∗ free_ports ip {[port]}
        (* the history of sent and received messages on [a] *)
        ∗ a ⤳ (∅, ∅) }}}
      ping #a #b @[ip]
    {{{ v m, RET #"PONG";
        ⌜v = #(m_body m)⌝ ∗ a ⤳ ({[m]}, {[ mkMessage a b "PING" ]})}}}.
  Proof.
    iIntros (-> -> Φ) "(#Hpong & Hunallocated & Hip & Ha) HΦ".
    wp_lam.
    wp_let.
    wp_socket sh as "Hh".
    wp_let.
    wp_apply (aneris_wp_socket_interp_alloc_singleton ping_protocol with "Hunallocated").
    iIntros "#Hping".
    wp_socketbind.
    wp_send.
    { iExists _. simpl. iFrame "#". auto. }
    wp_seq.
    wp_apply (aneris_wp_receivefrom with "[$Ha $Hping $Hh]"); [done|done|done|].
    iIntros (m) "[%Hdest [(% & Hh & Ha & _ & %Hm) | (% & Hh & Ha)]]".
    2: { (* Since no messages have been received yet, a duplicate is not possible
            and we get a contradiction *)
         done. }
    rewrite Hm.
    wp_apply wp_unSOME; [done|].
    iIntros "_".
    wp_proj.
    iApply ("HΦ" $! _ m).
    rewrite 2!right_id_L.
    iFrame.
    done.
  Qed.

End ping.


(** We now define a closed system with a distinguished system node that spawns
    the [pong] and [ping] nodes.  *)
Definition ping_pong_runner : expr :=
  let: "pongaddr" := MakeAddress #"0.0.0.0" #80 in
  let: "pingaddr" := MakeAddress #"0.0.0.1" #80 in
  Start "0.0.0.0" (pong "pongaddr") ;;
  Start "0.0.0.1" (ping "pingaddr" "pongaddr").

Definition pong_addr := SocketAddressInet "0.0.0.0" 80.
Definition ping_addr := SocketAddressInet "0.0.0.1" 80.

Definition ips : gset string := {[ ip_of_address pong_addr ; ip_of_address ping_addr ]}.

Section ping_pong_runner.
  Context `{dG : anerisG Σ}.

  Lemma ping_pong_runner_spec :
    {{{  (* empty message histories for the addresses *)
         pong_addr ⤳ (∅, ∅)
         ∗ ping_addr ⤳ (∅, ∅)
         (* no socket protocols have been allocated for the addresses *)
         ∗ unallocated {[pong_addr]}
         ∗ unallocated {[ping_addr]}
         (* the ips are free *)
         ∗ free_ip (ip_of_address pong_addr)
         ∗ free_ip (ip_of_address ping_addr) }}}
      ping_pong_runner @["system"]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "(Hponga & Hpinga & Hpo & Hpi & Hpongip & Hpingip) HΦ".
    rewrite /ping_pong_runner.
    wp_pures.
    (* allocate [pong]'s socket protocol  *)
    wp_apply (aneris_wp_socket_interp_alloc_singleton pong_protocol with "Hpo").
    iIntros "#Hpong".
    wp_apply (aneris_wp_start {[80%positive]}); eauto.
    iFrame.
    iSplitR "Hponga".
    2: { iIntros "!> Hp". wp_apply (pong_spec with "[$Hp $Hponga $Hpong]"); done. }
    iModIntro. wp_pures.
    wp_apply (aneris_wp_start {[80%positive : port]}); eauto.
    iFrame.
    iSplitL "HΦ".
    { by iApply "HΦ". }
    iIntros "!> Hp".
    iApply (ping_spec with "[$Hp $Hpi $Hpinga] []"); eauto.
  Qed.

End ping_pong_runner.

(** The initial state  *)
Definition ping_pong_is :=
  {|
    state_heaps :=  {["system" := ∅ ]};
    state_sockets := {["system" := ∅ ]};
    state_ms := ∅;
    state_trace := [];
  |}.

(** This soundness theorem tells us---without relying on Aneris or Iris---that
    the closed system is *safe*, i.e., it doesn't get stuck/crash.  *)
Theorem ping_pong_safe :
  aneris_adequate ping_pong_runner "system" ping_pong_is (λ _, True).
Proof.
  set (Σ := #[anerisΣ unit_model]).
  apply (no_model.adequacy_hoare_no_model_simpl Σ ips {[ pong_addr; ping_addr ]}); try set_solver.
  iIntros (dinvG).
  iIntros (?) "!# (Hf & Hhist & Hips) HΦ".
  iDestruct (unallocated_split with "Hf") as "[Hf1 Hf2]"; [set_solver|].
  rewrite (big_sepS_delete _ _ "0.0.0.0"); [|set_solver].
  rewrite (big_sepS_delete _ _ "0.0.0.1"); [|set_solver].
  iDestruct "Hips" as "(? & ? & _)".
  rewrite (big_sepS_delete _ _ pong_addr); [|set_solver].
  rewrite (big_sepS_delete _ _ ping_addr); [|set_solver].
  iDestruct "Hhist" as "(Hpong & Hping & _)".
  wp_apply (ping_pong_runner_spec with "[$] [$]").
Qed.
