open !Ast
open Serialization_code
open List_code
open Oplib_code
open Map_comb_code
open Lwwreg_code

(* A table of multi valued registers. *)

type 'valTy table_of_lwwregs_opTy = ('valTy writeOpTy) map_comb_opTy
type 'valTy table_of_lwwregs_stTy = ('valTy lwwreg) map_comb_stTy

let table_of_lwwregs_effect (msg : ('valTy table_of_lwwregs_opTy) msgTy) (st : 'valTy table_of_lwwregs_stTy) = map_comb_effect lwwreg_init_st lwwreg_effect msg st

let table_of_lwwregs_init_st () = map_comb_init_st ()

let table_of_lwwregs_crdt : ('valTy table_of_lwwregs_opTy, 'valTy table_of_lwwregs_stTy) crdtTy = fun () -> (table_of_lwwregs_init_st, table_of_lwwregs_effect)

let table_of_lwwregs_init (val_ser[@metavar]) (val_deser[@metavar]) (addrs : saddr alist) (rid : repIdTy) =
  let initRes = oplib_init (prod_ser string_ser val_ser) (prod_deser string_deser val_deser) addrs rid table_of_lwwregs_crdt in
  let (get_state, update) = initRes in
  (get_state, update)
