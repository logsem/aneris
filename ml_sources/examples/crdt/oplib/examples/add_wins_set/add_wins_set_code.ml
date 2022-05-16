open !Ast
open List_code
open Vector_clock_code
open Serialization_code
open Oplib_code

(* Add-wins-set CRDT. If there are an add and a remove operation that are incomparable in time, the add operation wins. *)

type 'valTy stTy  = ('valTy * vector_clock) alist
type 'valTy opTy = ('valTy, 'valTy) sumTy (* left is add, right is remove. *)


let init_st () : 'valTy stTy = list_nil

let effect (msg : 'valTy opTy msgTy) (st : 'valTy stTy) =
  let ((v, vc), _u) = msg in
  match v with
  | InjL w -> list_cons (w, vc) st
  | InjR w ->
    let should_keep p =
      if (fst p = w) then
        let vc' = snd p in
        not (vect_leq vc' vc) (* keep only if it was not added before *)
      else
        true
    in
    list_filter should_keep st

let aws_crdt : ('valTy opTy, 'valTy stTy) crdtTy = fun () -> (init_st, effect)

let aws_init (val_ser[@metavar]) (val_deser[@metavar]) addrs rid =
  let initRes = oplib_init (sum_ser val_ser val_ser) (sum_deser val_deser val_deser) addrs rid aws_crdt in
  let (get_state, update) = initRes in
  (get_state, update)
