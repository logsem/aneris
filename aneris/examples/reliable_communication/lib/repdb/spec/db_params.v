From RecordUpdate Require Import RecordSet.
From aneris.aneris_lang Require Import network resources.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.

Definition Key := string.

(** Arguments that user supplies to the interface *)

Class DB_params := {
  DB_addr :  socket_address;
  DB_addrF :  socket_address;
  DB_keys : gset Key;
  DB_InvName : namespace;
  DB_serialization : serialization;
  DB_ser_inj : ser_is_injective DB_serialization;
  DB_ser_inj_alt : ser_is_injective_alt DB_serialization;
}.

Notation DB_Serializable v := (Serializable DB_serialization v).

Record SerializableVal `{!DB_params} :=
  SerVal {SV_val : val;
          SV_ser : DB_Serializable SV_val }.

Coercion SV_val : SerializableVal >-> val.

Existing Instance SV_ser.

Arguments SerVal {_} _ {_}.
