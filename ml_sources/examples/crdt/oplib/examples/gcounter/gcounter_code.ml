open !Ast
open Serialization_code
open List_code
open Oplib_code

(* A positive-negative (PN) counter CRDT.
   A PN-Counter's state is just an integers.
   The counter can be incremented and decremented by
   an arbitrary amount. *)

type opTy = int (* the delta (positive or negative) by which to modify the counter *)
type stTy = int (* the state of the counter is its value *)

let effect (msg : opTy msgTy) (counter : stTy) =
  let ((delta, _x), _y) = msg in
  assert (0 <= delta);
  counter + delta

let init_st () = 0

let counter_crdt : (opTy, stTy) crdtTy = fun () -> (init_st, effect)

let counter_init (addrs : saddr alist) (rid : repIdTy) =
  let initRes = oplib_init int_ser int_deser addrs rid counter_crdt in
  let (get_state, update) = initRes in
  (get_state, update)
