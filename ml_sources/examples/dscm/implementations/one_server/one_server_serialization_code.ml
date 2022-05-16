open !Ast
open Serialization_code

(** Serialization *)

(* let clntId_serializer = saddr_serializer *)
let seqId_serializer = int_serializer

let write_serializer (val_ser[@metavar]) =
  prod_serializer string_serializer val_ser

let read_serializer = string_serializer

(* ⟨REQUEST op, c, s⟩ *)
let request_serializer (val_ser[@metavar]) =
  prod_serializer
    (sum_serializer (write_serializer val_ser) read_serializer)
    seqId_serializer

(* ⟨REPLY s, x, c⟩ *)
let reply_serializer (val_ser[@metavar]) =
  prod_serializer
    (sum_serializer (unit_serializer) (option_serializer val_ser))
    seqId_serializer
