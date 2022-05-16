From RecordUpdate Require Import RecordSet.
From aneris.aneris_lang Require Import network resources.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.

(** Arguments that user supplies to the interface *)

Class RCB_params := {
  RCB_addresses : list socket_address;
  RCB_addresses_NoDup : NoDup RCB_addresses;
  RCB_InvName : namespace;
  RCB_serialization : serialization;
}.

Notation RCB_Serializable v := (Serializable RCB_serialization v).

Record SerializableVal `{!RCB_params} :=
  SerVal {SV_val : val;
          SV_ser : RCB_Serializable SV_val }.

Coercion SV_val : SerializableVal >-> val.

Existing Instance SV_ser.

Arguments SerVal {_} _ {_}.
