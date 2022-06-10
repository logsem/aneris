From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import serialization_proof lock_proof.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.spec Require Import resources.

From actris.channel Require Import proto.
From stdpp Require Import base tactics telescopes.

Set Default Proof Using "Type".

Canonical Structure valO := leibnizO val.
Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).


Section API_spec.
  Context `{ !anerisG Mdl Σ }.
  Context `{ !@Chan_mapsto_resource Σ}.
  Context `{ UP : !Reliable_communication_service_params}.
  Context `{ !SessionResources UP}.

  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Notation clt_ser := RCParams_clt_ser.
  Notation srv_ser := RCParams_srv_ser.
  Notation srv_saddr := RCParams_srv_saddr.
  Notation srv_si := reserved_server_socket_interp.
  Notation srv_ip := (ip_of_address srv_saddr).

  Definition make_client_skt_spec (clt_addr : socket_address) (A : gset socket_address) : Prop :=
    {{{ ⌜clt_addr ∉ A⌝ ∗
        clt_addr ⤳ (∅, ∅)  ∗
        free_ports (ip_of_address clt_addr) {[port_of_address clt_addr]} ∗
        RCParams_srv_saddr ⤇ srv_si ∗
        fixed A
    }}}
       make_client_skt (s_serializer clt_ser) (s_serializer srv_ser) #clt_addr
       @[ip_of_address clt_addr]
    {{{ skt, RET skt; CltCanConnect skt clt_addr }}}.

  Definition make_server_skt_spec A : Prop :=
    {{{ srv_saddr ⤇ srv_si ∗
        ⌜RCParams_srv_saddr ∈ A⌝ ∗
        fixed A ∗
        RCParams_srv_saddr ⤳ (∅, ∅) ∗
        free_ports (srv_ip) {[port_of_address srv_saddr]} ∗
        SrvInit
    }}}
       make_server_skt (s_serializer srv_ser) (s_serializer clt_ser) #RCParams_srv_saddr
       @[srv_ip]
    {{{ skt, RET skt; SrvCanListen skt }}}.

  Definition server_listen_spec (skt : val) : Prop :=
    {{{ SrvCanListen skt }}}
       server_listen skt @[srv_ip]
    {{{ v, RET v; ⌜v = #()⌝ ∗ SrvListens skt }}}.

  Definition accept_spec (skt : val) : Prop :=
    {{{ SrvListens skt }}}
       accept skt @[srv_ip]
    {{{ c (client_addr: socket_address) v, RET v; ⌜v = (c, #client_addr)%V⌝ ∗
         SrvListens skt ∗
         c ↣{ srv_ip, RCParams_srv_ser } iProto_dual RCParams_protocol
    }}}.

  Definition connect_spec (skt : val) (clt_addr : socket_address) : Prop :=
    {{{ CltCanConnect skt clt_addr }}}
       connect skt #RCParams_srv_saddr @[ip_of_address clt_addr]
    {{{ c, RET c;
        c ↣{ ip_of_address clt_addr, RCParams_clt_ser } RCParams_protocol
    }}}.

  Definition send_spec (c : val) v p ip serA : Prop :=
    {{{ c ↣{ ip, serA } (<!> MSG v; p)%proto ∗ ⌜Serializable serA v⌝ }}}
      send c v @[ip]
    {{{ RET #(); c ↣{ ip, serA } p }}}.

  Definition send_spec_tele
      TT c (tt : TT)
      (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) ip serA : Prop :=
    {{{ c ↣{ ip , serA } (<!.. (x : TT) > MSG (v x) {{ P x }}; p x)%proto ∗ P tt ∗
        ⌜Serializable serA (v tt)⌝ }}}
      send c (v tt) @[ip]
    {{{ RET #(); c ↣{ ip , serA } (p tt)%proto }}}.

  Definition try_recv_spec
    TT (c : val) (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) ip ser
     : Prop :=
    {{{ c ↣{ ip , ser } (<?.. x> MSG (v x) {{ P x }}; p x)%proto }}}
      try_recv c @[ip]
    {{{ w, RET w; (⌜w = NONEV⌝ ∗ c ↣{ ip, ser } (<?.. x> MSG (v x) {{ P x }}; p x)%proto) ∨
                   (∃ x : TT,  ⌜w = SOMEV (v x)⌝ ∗ c ↣{ ip, ser } (p x)%proto ∗ P x) }}}.

  Definition recv_spec TT c (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) ip ser
     : Prop :=
    {{{ c ↣{ ip, ser } (<?.. x> MSG (v x) {{ ▷ P x }}; p x)%proto }}}
      recv c @[ip]
    {{{ x, RET v x; c ↣{ ip, ser } p x ∗ P x }}}.

End API_spec.

Arguments make_client_skt_spec {_ _ _}.
Arguments connect_spec {_ _ _ _}.
Arguments make_server_skt_spec {_ _ _}.
Arguments server_listen_spec {_ _ _}.
Arguments accept_spec {_ _ _ _}.
Arguments send_spec {_ _ _ _}.
Arguments try_recv_spec {_ _ _ _}.
Arguments recv_spec {_ _ _ _}.

Section Init.
  Context `{!anerisG Mdl Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Class Reliable_communication_init := {
      Reliable_communication_init_setup
        E (UP : Reliable_communication_service_params):
      ↑RCParams_srv_N ⊆ E →
      ⊢ |={E}=>
        ∃ ( _ : Chan_mapsto_resource),
        ∃ (SnRes : SessionResources UP),
          SrvInit ∗
          ⌜(∀ sa A, make_client_skt_spec UP SnRes sa A)⌝ ∗
          ⌜(∀ A, make_server_skt_spec UP SnRes A)⌝ ∗
          ⌜(∀ skt sa, connect_spec UP SnRes skt sa)⌝ ∗
          ⌜(∀ skt, server_listen_spec UP SnRes skt)⌝ ∗
          ⌜(∀ skt, accept_spec UP SnRes skt)⌝ ∗
          ⌜(∀ c v p ip ser, send_spec c v p ip ser)⌝ ∗
          ⌜(∀ TT c t v P q ip s, send_spec_tele TT c t v P q ip s)⌝ ∗
          ⌜(∀ TT c v P q ip ser, try_recv_spec TT c v P q ip ser)⌝ ∗
          ⌜(∀ TT c v P q ip ser, recv_spec TT c v P q ip ser)⌝
    }.

End Init.

(* TODO: Either get rid of this class or find a way to manipulate ghost names. *)
Section Reliable_communication_Specified_API_def.
  Context
    `{ !anerisG Mdl Σ,
       !lockG Σ,
       @Chan_mapsto_resource Σ}.

  Class Reliable_communication_Specified_API_network
        `{ UP : !Reliable_communication_service_params}
        `{!SessionResources UP}
    := {
      RCSpec_make_client_skt_spec sa A: make_client_skt_spec _ _ sa A;
      RCSpec_make_server_skt_spec A : make_server_skt_spec _ _ A;
      RCSpec_connect_spec skt sa : connect_spec _ _ skt sa;
      RCSpec_server_listen_spec skt : server_listen_spec _ _ skt;
      RCSpec_accept_spec skt : accept_spec _ _ skt;
    }.

  Class Reliable_communication_Specified_API_session := {
      RCSpec_send_spec c v p ip ser : send_spec c v p ip ser;
      RCSpec_send_spec_tele TT c t v P q ip s : send_spec_tele TT c t v P q ip s;
      RCSpec_try_recv_spec TT c v P q ip ser : try_recv_spec TT c v P q ip ser;
      RCSpec_recv_spec TT c v P q ip ser : recv_spec TT c v P q ip ser
    }.

End Reliable_communication_Specified_API_def.

(** Reliable_communication_Specified_API *)
(*     : Reliable_communication_service_params → SessionResources → Prop *)
Arguments Reliable_communication_Specified_API_network { _ _ _ _ }.
Arguments Reliable_communication_Specified_API_session { _ _ _ }.
