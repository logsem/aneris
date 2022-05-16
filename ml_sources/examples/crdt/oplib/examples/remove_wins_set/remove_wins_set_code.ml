open !Ast
open List_code
open Vector_clock_code
open Serialization_code
open Oplib_code

(* Remove-wins-set CRDT. If there are an add and a remove operation that are incomparable in time, the remove operation wins. *)

type 'valTy stTy  = ('valTy * vector_clock) alist * ('valTy * vector_clock) alist (* Pairs consisting of the set of elements, and the set of deleted elements. *)
type 'valTy opTy = ('valTy, 'valTy) sumTy (* left is add, right is remove. *)


let init_st () : 'valTy stTy = (list_nil, list_nil)

let effect_remove_op v vc (st : 'valTy stTy) =
  let (contents, removes) = st in
  let updated_removes = list_cons (v, vc) removes in
  let should_keep_in_contents p =
    if (fst p = v) then
      let vc' = snd p in
      (vect_leq vc vc') (* keep only if it was added after the current remove *)
    else
      true
  in
  let updated_contents = list_filter should_keep_in_contents contents in
  (updated_contents, updated_removes)

let effect_add_op v vc (st : 'valTy stTy) =
  let (contents, removes) = st in
  let permits_add r =
    if (fst r = v) then
      let vc' = snd r in
      (vect_leq vc' vc) (* add is permited if the delete operation is before the current add operation. *)
    else
      true
  in
  let should_add = list_fold (fun p r -> p && (permits_add r)) true removes in
  let updated_contents = if should_add then list_cons (v, vc) contents else contents in
  (updated_contents, removes)


let effect (msg : 'valTy opTy msgTy) (st : 'valTy stTy) =
  let ((v, vc), _u) = msg in
  match v with
  | InjL w -> effect_add_op w vc st
  | InjR w -> effect_remove_op w vc st

let rws_crdt : ('valTy opTy, 'valTy stTy) crdtTy = fun () -> (init_st, effect)

let rws_init (val_ser[@metavar]) (val_deser[@metavar]) addrs rid =
  let initRes = oplib_init (sum_ser val_ser val_ser) (sum_deser val_deser val_deser) addrs rid rws_crdt in
  let (get_state, update) = initRes in
  (get_state, update)
