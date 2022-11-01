open !Ast
open Serialization_code
open List_code
open Set_code
open Statelib_code

type 'a stTy = 'a aset

let mutator : ('a, 'stTy) mutatorFnTy =
  fun (_i : int) (gs : 'stTy) (op : 'a) ->
  set_add op gs

(* TODO: move to the aneris lib. *)
let set_union (s1 : 'a aset) (s2 : 'a aset) : 'a aset =
  set_foldl (fun su e -> set_add e su) s1 s2

(* TODO: move to the aneris lib. *)
let set_serializer (elt_ser[@metavar "serializer"] : 'a serializer) : 'a aset serializer =
  list_serializer elt_ser


let merge (st1 : 'a stTy) (st2 : 'a stTy) : 'a stTy =
  set_union st1 st2

let eval_state (st : 'a stTy) = st

let init_st () = set_empty ()

let gos_crdt : ('a, 'a stTy) crdtTy = fun () -> ((init_st, mutator), merge)

let st_ser (elt_ser[@metavar "serializer"] : 'a serializer) : 'a alist serializer =
  set_serializer elt_ser

let gos_init (elt_ser[@metavar "serializer"] : 'a serializer) (addrs : saddr alist) (rid : int) =
  let initRes =
    statelib_init (st_ser elt_ser).s_ser (st_ser elt_ser).s_deser addrs rid gos_crdt in
  let (get_state, update) = initRes in
  let eval st = eval_state (get_state st) in
  (eval, update)
