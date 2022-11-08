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

let merge (st1 : 'a stTy) (st2 : 'a stTy) : 'a stTy =
  set_union st1 st2

let eval_state (st : 'a stTy) = st

let init_st () = set_empty ()

let gos_crdt : ('a, 'a stTy) crdtTy = fun () -> ((init_st, mutator), merge)

let gos_init  (elt_ser[@metavar "val"])(elt_deser[@metavar "val"])
    (addrs : saddr alist) (rid : int) =
  let initRes =
    statelib_init (list_ser elt_ser) (list_deser elt_deser) addrs rid gos_crdt in
  let (get_state, update) = initRes in
  (get_state, update)
