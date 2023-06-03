From RecordUpdate Require Import RecordSet.
From aneris.aneris_lang Require Import network resources.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.

Definition Key := string.

(** Arguments that user supplies to the interface *)

Class User_params := {
  KVS_address : socket_address;
  KVS_keys : gset Key;
  KVS_InvName : namespace;
  KVS_serialization : serialization;
}.

Notation KVS_Serializable v := (Serializable KVS_serialization v).

Record SerializableVal `{!User_params} :=
  SerVal {SV_val : val;
          SV_ser : KVS_Serializable SV_val }.

Coercion SV_val : SerializableVal >-> val.

Existing Instance SV_ser.

Arguments SerVal {_} _ {_}.
