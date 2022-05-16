open !Ast
open Set_code
open Oplib_code

(* Grow only set CRDT. *)

type 'valTy stTy  = 'valTy aset
type 'valTy opTy = Add of 'valTy


let init_st () : 'valTy stTy = set_empty ()

let effect (msg : 'valTy opTy msgTy) (st : 'valTy stTy) =
  let ((v, _vc), _u) = msg in
  set_add v st

let gos_crdt : ('valTy opTy, 'valTy stTy) crdtTy = fun () -> (init_st, effect)

let gos_init (val_ser[@metavar]) (val_deser[@metavar]) addrs rid =
  let initRes = oplib_init val_ser val_deser addrs rid gos_crdt in
  let (get_state, update) = initRes in
  (get_state, update)
