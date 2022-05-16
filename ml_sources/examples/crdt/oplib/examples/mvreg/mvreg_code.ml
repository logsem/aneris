open !Ast
open Serialization_code
open List_code
open Vector_clock_code
open Oplib_code

(* Multi-value register. Concurrent writes are all kept. *)

type 'valTy mvreg = ('valTy * vector_clock) alist
type 'valTy writeOpTy = 'valTy (* `write v` *)

(* let op_ser (val_ser[@metavar]) = val_ser *)

(* let op_deser (val_deser[@metavar]) = val_deser *)

let init_st (): 'valTy mvreg = list_nil

let effect (msg : 'valTy writeOpTy msgTy) (reg : 'valTy mvreg) =
  let ((v, vc), _u) = msg in
  let vals =
    let is_conc = fun p ->
      let vc' = snd p in
      assert (not (vect_leq vc vc')); (* guaranteed by RCB and our locking *)
      vect_conc vc' vc (* keep all concurrent writes *)
    in
    list_filter is_conc reg
  in
  list_cons (v, vc) vals

let mvreg_crdt : ('valTy writeOpTy, 'valTy mvreg) crdtTy = fun () -> (init_st, effect)

let mvreg_init (* (val_ser[@metavar]) (val_deser[@metavar]) *) addrs rid =
  let initRes = oplib_init (* (op_ser val_ser) *) (* (op_deser val_deser) *) int_ser int_deser addrs rid mvreg_crdt in
  let (get_state, update) = initRes in
  (get_state, update)
