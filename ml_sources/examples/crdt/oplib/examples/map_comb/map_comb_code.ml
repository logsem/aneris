open !Ast
open Serialization_code
open Map_code
open List_code
open Oplib_code

(* A map combinator, which takes a CRDT and maeks the CRDT of maps where keys are strings and values are of the type of the given CRDT. *)

type 'a map_comb_opTy = string * 'a
type 'a map_comb_stTy = (string, 'a) amap

let map_comb_effect (init : unit -> 'a) (eff : ('a, 'b) effectFnTy) (msg : 'a map_comb_opTy msgTy) (state : 'b map_comb_stTy) =
  let (((key, delta), vc), origin) = msg in
  let cur_st_wo =
    match map_lookup key state with
    | None -> (init (), state)
    | Some cur -> (cur, map_remove key state)
  in
  let (current, state_without) = cur_st_wo in
  let newval = eff ((delta, vc), origin) current in
  map_insert key newval state_without

let map_comb_init_st () = map_empty ()

let map_comb_crdt (crdt : ('a, 'b) crdtTy) : ('a map_comb_opTy, 'b map_comb_stTy) crdtTy =
  fun () ->
  let res = crdt () in
  let (is, eff) = res in
  (map_comb_init_st, map_comb_effect is eff)

let map_comb_init (ser[@metavar "val"]) (deser[@metavar "val"]) crdt (addrs : saddr alist) (rid : repIdTy) =
  let initRes = oplib_init (prod_ser string_ser ser) (prod_deser string_ser deser) addrs rid (map_comb_crdt crdt) in
  let (get_state, update) = initRes in
  (get_state, update)
