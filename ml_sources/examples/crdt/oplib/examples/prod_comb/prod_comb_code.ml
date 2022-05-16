open !Ast
open Serialization_code
open List_code
open Oplib_code

(* A product combinator, which takes two CRDTs and maeks the CRDT of pairs of
   states of the CRDTs. *)

type ('a, 'b) opTy = 'a * 'b
type ('a, 'b) stTy = 'a * 'b

let effect (eff1 : ('a, 'c) effectFnTy) (eff2 : ('b, 'd) effectFnTy) (msg : ('a, 'b) opTy msgTy) (state : ('c, 'd) stTy) =
  let (((delta1, delta2), vc), origin) = msg in
  let (st1, st2) = state in
  (eff1 ((delta1, vc), origin) st1, eff2 ((delta2, vc), origin) st2)

let init_st is1 is2 () = (is1 (), is2 ())

let prod_comb_crdt (crdt1 : ('a, 'c) crdtTy) (crdt2 : ('b, 'd) crdtTy) : (('a, 'b) opTy, ('c, 'd) stTy) crdtTy =
  fun () ->
  let res1 = crdt1 () in
  let res2 = crdt2 () in
  let (is1, eff1) = res1 in
  let (is2, eff2) = res2 in
  (init_st is1 is2, effect eff1 eff2)

let prod_comb_init (a_ser[@metavar "val"]) (a_deser[@metavar "val"]) (b_ser[@metavar "val"]) (b_deser[@metavar "val"]) crdt1 crdt2 (addrs : saddr alist) (rid : repIdTy) =
  let initRes = oplib_init (prod_ser a_ser b_ser) (prod_deser a_deser b_deser) addrs rid (prod_comb_crdt crdt1 crdt2) in
  let (get_state, update) = initRes in
  (get_state, update)
