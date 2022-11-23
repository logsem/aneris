open !Ast
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
  fun (i : int) (gs : pnCptStTy) (op : pnCptOpTy) ->
  prod_mutator gcpt_mutator gcpt_mutator i gs op

let pn_cpt_merge (st1 : pnCptStTy) (st2 : pnCptStTy) : pnCptStTy =
  prod_merge gcpt_merge gcpt_merge st1 st2

let pn_cpt_crdt n : (pnCptOpTy, pnCptStTy) crdtTy =
  fun () -> prod_crdt (gcpt_crdt n) (gcpt_crdt n) ()

let pn_cpt_init addrs rid =
  let len = list_length addrs in
  prod_init
    vect_serialize vect_deserialize
    vect_serialize vect_deserialize
    (gcpt_crdt len) (gcpt_crdt len) addrs rid

(** Step 2. PN counter wrapper. *)

(* TODO : move to List_code *)
let list_int_sum (l : int alist) =
  list_fold (fun acc n -> acc + n) 0 l

let pncounter_update (upd : pnCptOpTy -> unit) (n : int) =
  if 0 <= n
  then upd (n, 0)
  else upd (0, -n)

let pncounter_eval (get_state : unit -> pnCptStTy) () =
  let st = get_state () in
  let (pl, nl) = st in
  let p = list_int_sum pl in
  let n = list_int_sum nl in
  p - n

let pncounter_init addrs rid =
  let pn_cpt = pn_cpt_init addrs rid in
  let (get_st, upd_st) = pn_cpt in
  let get = pncounter_eval get_st in
  let upd = pncounter_update upd_st in
  (get, upd)
