From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From actris.channel Require Import proto.

Set Default Proof Using "Type".

Canonical Structure valO := leibnizO val.
Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

Class Reliable_communication_service_params `{ !anerisG Mdl Σ } :=
  { RCParams_clt_ser : serialization; (* client_send, server_receive *)
    RCParams_srv_ser : serialization; (* server_send, client_receive *)
    RCParams_srv_ser_inj : ser_is_injective RCParams_srv_ser;
    RCParams_srv_ser_inj_alt : ser_is_injective_alt RCParams_srv_ser;
    RCParams_clt_ser_inj : ser_is_injective RCParams_clt_ser;
    RCParams_clt_ser_inj_alt : ser_is_injective_alt RCParams_clt_ser;
    RCParams_srv_saddr : socket_address;
    RCParams_protocol : iProto Σ;
  }.

Arguments Reliable_communication_service_params {_ _ _}.
