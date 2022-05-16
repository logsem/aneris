open Ast
open Map_code
open Serialization_code
open Client_server_code


type 'a requestTy = (string * 'a, string) sumTy
type 'a replyTy = (unit, 'a option) sumTy
type 'a db_chan_descr = ('a replyTy, 'a requestTy) chan_descr
type 'a requestEventTy = 'a requestTy * 'a db_chan_descr
type 'a replyEventTy =  'a replyTy * 'a db_chan_descr
type 'a databaseTy = ((string, 'a) amap)

let write_serializer (val_ser[@metavar]) =
  prod_serializer string_serializer val_ser

let read_serializer = string_serializer

(* ⟨REQUEST op, c, s⟩ *)
let request_serializer (val_ser[@metavar]) =
  (sum_serializer (write_serializer val_ser) read_serializer)

(* ⟨REPLY s, x, c⟩ *)
let reply_serializer (val_ser[@metavar]) =
  (sum_serializer (unit_serializer) (option_serializer val_ser))
