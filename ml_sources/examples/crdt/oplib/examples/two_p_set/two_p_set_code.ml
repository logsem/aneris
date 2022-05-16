open !Ast
open Set_code
open Serialization_code
open Oplib_code

(* 2P set CRDT where elements can never be added once they are removed. *)

type 'valTy stTy  = ('valTy aset) * ('valTy aset)
type 'valTy opTy = ('valTy, 'valTy) sumTy


let init_st () : 'valTy stTy = (set_empty (), set_empty ())

let effect (msg : 'valTy opTy msgTy) (st : 'valTy stTy) =
  let ((v, _vc), _u) = msg in
  match v with
  | InjL w -> (set_add w (fst st),snd st)
  | InjR w -> (fst st, set_add w (snd st))

let tps_crdt : ('valTy opTy, 'valTy stTy) crdtTy = fun () -> (init_st, effect)

let tps_init (val_ser[@metavar]) (val_deser[@metavar]) addrs rid =
  let initRes = oplib_init (sum_ser val_ser val_ser) (sum_deser val_deser val_deser) addrs rid tps_crdt in
  let (get_state, update) = initRes in
  (get_state, update)
