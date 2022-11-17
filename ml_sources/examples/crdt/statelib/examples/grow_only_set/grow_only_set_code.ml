open !Ast
open Serialization_code
open List_code
open Set_code
open Statelib_code

type 'a stTy = 'a aset

let gos_init_st () = set_empty ()

let gos_mutator : ('a, 'stTy) mutatorFnTy =
  fun (_i : int) (gs : 'stTy) (op : 'a) ->
  set_add op gs

let gos_merge (st1 : 'a stTy) (st2 : 'a stTy) : 'a stTy =
  set_union st1 st2

let gos_crdt : ('a, 'a stTy) crdtTy =
  fun () -> ((gos_init_st, gos_mutator), gos_merge)

let gos_init  (elt_ser[@metavar "val"]) (elt_deser[@metavar "val"])
    (addrs : saddr alist) (rid : int) =
  let initRes =
    statelib_init (list_ser elt_ser) (list_deser elt_deser)
      addrs rid gos_crdt in
  let (get_state, update) = initRes in
  (get_state, update)
