open !Ast
open Serialization_code
open List_code
open Oplib_code

(* A positive-negative (PN) counter CRDT.
   A PN-Counter's state is just an integers.
   The counter can be incremented and decremented by
   an arbitrary amount. *)

type pncounter_opTy = int (* the delta (positive or negative) by which to modify the counter *)
type pncounter_stTy = int (* the state of the counter is its value *)

let pncounter_effect (msg : pncounter_opTy msgTy) (counter : pncounter_stTy) =
  let ((delta, _x), _y) = msg in
  counter + delta

let pncounter_init_st () = 0

let pncounter_crdt : (pncounter_opTy, pncounter_stTy) crdtTy = fun () -> (pncounter_init_st, pncounter_effect)

let pncounter_init (addrs : saddr alist) (rid : repIdTy) =
  let initRes = oplib_init int_ser int_deser addrs rid pncounter_crdt in
  let (get_state, update) = initRes in
  (get_state, update)
