open !Ast
open Serialization_code
open List_code
open Statelib_code

(* A product combinator, which takes two CRDTs and makes the CRDT of pairs of
   states of the CRDTs. *)

type ('stA, 'stB) stProdTy = 'stA * 'stB
type ('opA, 'opB) opProdTy = 'opA * 'opB

type ('opA, 'opB, 'stA, 'stB) mutatorProdFnTy =
  (('opA, 'opB) opProdTy, ('stA, 'stB) stProdTy) mutatorFnTy

type ('stA, 'stB) init_stProdFnTy = unit -> ('stA, 'stB) stProdTy

type ('stA, 'stB) mergeProdFnTy = ('stA * 'stB) mergeFnTy

type  ('opA, 'opB, 'stA, 'stB) crdtProdTy =
  (('opA, 'opB) opProdTy, ('stA, 'stB) stProdTy) crdtTy
(* *   unit ->
 *   (((unit -> ('stA, 'stB) stProdTy) *
 *     ('opA, 'opB, 'stA, 'stB) mutatorProdFnTy) *
 *     ('stA, 'stB) mergeProdFnTy) *)

let prod_init_st init_fnA init_fnB : ('stA, 'stB) init_stProdFnTy =
  fun () -> (init_fnA (), init_fnB ())

let prod_mutator
    (mut_fnA : ('opA, 'stA) mutatorFnTy)
    (mut_fnB : ('opB, 'stB) mutatorFnTy)
  : ('opA, 'opB, 'stA, 'stB) mutatorProdFnTy =
  fun i gs op ->
  let (gsA, gsB) = gs in
  let (opA, opB) = op in
  (mut_fnA i gsA opA, mut_fnB i gsB opB)

let prod_merge
    (merge_fnA : 'stA mergeFnTy)
    (merge_fnB : 'stB mergeFnTy)
  : ('stA, 'stB) mergeProdFnTy =
   fun (st1 : ('stA, 'stB) stProdTy) (st2 : ('stA, 'stB) stProdTy) ->
   let (st11, st12) = st1 in
   let (st21, st22) = st2 in
   let mA = merge_fnA st11 st21 in
   let mB = merge_fnB st12 st22 in
   (mA, mB)

let prod_crdt
  (cA : ('opA, 'stA) crdtTy)
  (cB : ('opB, 'stB) crdtTy)
  :  (('opA, 'opB) opProdTy, ('stA, 'stB) stProdTy) crdtTy =
  (* :  ('opA, 'opB, 'stA, 'stB) crdtProdTy = *)
  fun () ->
  let cAp = cA () in
  let cBp = cB () in
  let ((init_fnA, mut_fnA), merge_fnA) = cAp in
  let ((init_fnB, mut_fnB), merge_fnB) = cBp in
  let init_fn = (fun () -> prod_init_st init_fnA init_fnB ()) in
  let mut_fn = (fun i gs op -> prod_mutator mut_fnA mut_fnB i gs op) in
  let merge_fn = (fun st1 st2 -> prod_merge merge_fnA merge_fnB st1 st2) in
  ((init_fn, mut_fn), merge_fn)

let prod_init
    (stA_ser[@metavar "val"]) (stA_deser[@metavar "val"])
    (stB_ser[@metavar "val"]) (stB_deser[@metavar "val"])
    (cA : ('opA, 'stA) crdtTy)
    (cB : ('opB, 'stB) crdtTy)
    (addrs : saddr alist) (rid : int) =
  let initRes =
    statelib_init
      (prod_ser stA_ser stB_ser)
      (prod_deser stA_deser stB_deser)
      addrs rid (fun () -> prod_crdt cA cB ()) in
  let (get_state, update) = initRes in
  (get_state, update)
