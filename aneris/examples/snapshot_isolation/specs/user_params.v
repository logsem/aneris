From RecordUpdate Require Import RecordSet.
From aneris.aneris_lang Require Import network resources.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.

Definition Key := string.

(** Arguments that user supplies to the interface *)

Class User_params := {
  KVS_address : socket_address;
  KVS_keys : gset Key;
  KVS_InvName : namespace;
  KVS_serialization : serialization;
  KVS_ser_inj : ser_is_injective KVS_serialization;
  KVS_ser_inj_alt : ser_is_injective_alt KVS_serialization
}.

Notation KVS_Serializable v := (Serializable KVS_serialization v).

Record SerializableVal `{!User_params} :=
  SerVal {SV_val : val;
          SV_ser : KVS_Serializable SV_val }.

Coercion SV_val : SerializableVal >-> val.

Existing Instance SV_ser.

Arguments SerVal {_} _ {_}.
