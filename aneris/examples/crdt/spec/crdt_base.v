From RecordUpdate Require Import RecordSet.
From aneris.aneris_lang Require Import network resources.

(** * Generic CRDT interface parameters *)

Class CRDT_Params := {
  CRDT_Addresses : list socket_address;
  CRDT_Addresses_NoDup : NoDup CRDT_Addresses;
  CRDT_InvName : namespace;
}.
