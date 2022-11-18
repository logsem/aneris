open !Ast
open Serialization_code
open Set_code
open Map_code
open List_code
open Statelib_code

(* A map combinator, which takes a CRDT and maeks the CRDT of maps where keys are strings and values are of the type of the given CRDT. *)

type 'op map_comb_opTy = string * 'op
type 'st map_comb_stTy = (string, 'st) amap
type ('op, 'st) map_comb_mutatorFnTy =
  ('op map_comb_opTy, 'st map_comb_stTy) mutatorFnTy
type 'st map_comb_mergeFnTy = 'st map_comb_stTy mergeFnTy
type  ('op, 'st) map_comb_crdtProdTy =
  ('op map_comb_opTy, 'st map_comb_stTy) crdtTy


let map_comb_init_st : unit -> 'st map_comb_stTy =
  fun () -> map_empty ()

let map_comb_mutator
    (init_st_fn : unit -> 'st)
    (mut_fn : ('op, 'st) mutatorFnTy)
  : ('op, 'st) map_comb_mutatorFnTy
  = fun (i : int) (st : 'st map_comb_stTy) (op : 'op map_comb_opTy) ->
    let (k, k_op) = op in
    let k_st' =
      match map_lookup k st with
      | None -> mut_fn i (init_st_fn ()) k_op
      | Some k_st -> mut_fn i k_st k_op
    in
    map_insert k k_st' st

(* let map_comb_merge
    (merge_fn : 'st mergeFnTy) : 'st map_comb_mergeFnTy =
  fun (st0 : 'st map_comb_stTy) (st0' : 'st map_comb_stTy) ->
  let rec aux : 'st map_comb_mergeFnTy =
    fun (st : 'st map_comb_stTy) (st' : 'st map_comb_stTy) ->
      match st with
      | None -> st'
      | Some p ->
        let (kv, st_tl) = p in
        let (k,v) = kv in
        match map_lookup k st' with
        | None ->
          let res = aux st_tl st' in
          map_insert k v res
        | Some v' ->
          let vres = merge_fn v v' in
          let st'' = map_insert k vres st' in
          aux st_tl st''
  in aux st0 st0' *)

let map_comb_merge
    (merge_fn : 'st mergeFnTy) : 'st map_comb_mergeFnTy =
  fun (st0 : 'st map_comb_stTy) (st1 : 'st map_comb_stTy) ->
  let dom0 = map_dom st0 in
  let dom1 = map_dom st1 in
  let dom = set_union dom0 dom1 in
  let merge_aux m k =
    match map_lookup k st0 with
    | None ->
      begin
        match map_lookup k st1 with
        | None -> assert false
        | Some v1 -> map_insert k v1 m
      end
    | Some v0 ->
      begin
        match map_lookup k st1 with
        | None -> map_insert k v0 m
        | Some v1 -> map_insert k (merge_fn v0 v1) m
      end
  in set_foldl merge_aux (map_empty ()) dom


let map_comb_crdt
  (cA[@metavar "val"] : ('op, 'st) crdtTy) : ('op, 'st) map_comb_crdtProdTy =
  fun () ->
  let cAp = cA () in
  let ((init_fnA, mut_fnA), merge_fnA) = cAp in
  let mut_fn = (fun i gs op -> map_comb_mutator init_fnA mut_fnA i gs op) in
  let merge_fn = (fun st1 st2 -> map_comb_merge merge_fnA st1 st2) in
  ((map_comb_init_st, mut_fn), merge_fn)

let string_map_ser (stA_ser[@metavar "val"]) =
  list_ser (prod_ser string_ser stA_ser)

let string_map_deser (stA_deser[@metavar "val"]) =
  list_deser (prod_deser string_deser stA_deser)

let map_comb_init
    (stA_ser[@metavar "val"]) (stA_deser[@metavar "val"])
    (cA[@metavar "val"] : ('op, 'st) crdtTy)
    (addrs : saddr alist) (rid : int) =
  let initRes =
    statelib_init
      (string_map_ser stA_ser)
      (string_map_deser stA_deser)
      addrs rid (fun () -> map_comb_crdt cA ()) in
  let (get_state, update) = initRes in
  ((get_state : unit -> 'st map_comb_stTy),
   (update : 'op map_comb_opTy -> unit))
