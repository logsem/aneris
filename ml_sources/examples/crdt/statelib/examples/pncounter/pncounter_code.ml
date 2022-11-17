open !Ast
open Serialization_code
open List_code
open Vector_clock_code
open Statelib_code
open Gcounter_code
open Prod_comb_code

(** Step 1. Raw PN counter using product and gcpt crdts. *)

type pnCptStTy = (int alist, int alist) stProdTy
type pnCptOpTy = (int, int) opProdTy

let pn_cpt_init_st n : unit -> pnCptStTy =
  fun () -> prod_init_st (gcpt_init_st n) (gcpt_init_st n) ()

let pn_cpt_mutator : (pnCptOpTy, pnCptStTy) mutatorFnTy =
  fun (i : int) (cpt : pnCptStTy) (op : pnCptOpTy) ->
  let (p, n) = op in
  assert ((0 = p && 0 = n) || (p < 0 && n = 0) || (n < 0 && p = 0));
  prod_mutator gcpt_mutator gcpt_mutator i cpt op

let pn_cpt_merge (st : pnCptStTy) (st' : pnCptStTy) : pnCptStTy =
  prod_merge gcpt_merge gcpt_merge st st'


let pn_cpt_crdt n : (pnCptOpTy, pnCptStTy) crdtTy =
  fun () -> ((pn_cpt_init_st n, pn_cpt_mutator), pn_cpt_merge)

let pn_cpt_init addrs rid =
  let len = list_length addrs in
  let initRes =
    statelib_init
      (prod_ser vect_serialize vect_serialize)
      (prod_deser vect_deserialize vect_deserialize)
      addrs rid (pn_cpt_crdt len) in
  let get_state = fst initRes in
  let update = snd initRes in
  (get_state, update)

(** Step 2. PN counter wrapper. *)

(* TODO : move to List_code *)
let list_int_sum (l : int alist) =
  list_fold (fun acc n -> acc + n) 0 l

let pncounter_update (upd : pnCptOpTy -> unit) (n : int) =
  if 0 <= n
  then upd (n, 0)
  else upd (0, n)

let pncounter_eval (get_state : unit -> pnCptStTy) () =
  let st = get_state () in
  let (pl, nl) = st in
  let p = list_int_sum pl in
  let n = list_int_sum nl in
  p + n

let pncounter_init addrs rid =
  let pn_cpt = pn_cpt_init addrs rid in
  let (get_st, upd_st) = pn_cpt in
  let get = pncounter_eval get_st in
  let upd = pncounter_update upd_st in
  (get, upd)
