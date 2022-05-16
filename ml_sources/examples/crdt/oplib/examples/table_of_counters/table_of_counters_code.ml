open !Ast
open Serialization_code
open List_code
open Oplib_code
open Map_comb_code
open Pncounter_code

(* A table of positive-negative counters. *)

type opTy = pncounter_opTy map_comb_opTy
type stTy = pncounter_stTy map_comb_stTy

let table_of_counters_effect (msg : opTy msgTy) (st : stTy) = map_comb_effect pncounter_init_st pncounter_effect msg st

let table_of_counters_init_st () = map_comb_init_st ()

let table_of_counters_crdt : (opTy, stTy) crdtTy = fun () -> (table_of_counters_init_st, table_of_counters_effect)

let table_of_counters_init (addrs : saddr alist) (rid : repIdTy) =
  let initRes = oplib_init (prod_ser string_ser int_ser) (prod_deser string_deser int_deser) addrs rid table_of_counters_crdt in
  let (get_state, update) = initRes in
  (get_state, update)
