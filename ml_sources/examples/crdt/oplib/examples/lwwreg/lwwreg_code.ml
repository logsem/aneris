open !Ast
open Vector_clock_code
open Oplib_code

(* Last-writer-wins register. Ties are broken by highest origin id. *)

type 'valTy lwwreg = (('valTy * vector_clock) * int) option
type 'valTy writeOpTy = 'valTy (* `write v` *)

let lwwreg_init_st (): 'valTy lwwreg = None

(* Converts a vector clock into a Lamport timestamp (a scalar that is
   compatible with causal order) by adding the vc's components. *)
let rec vc_to_lamport (vc : vector_clock) : int =
  match vc with
  | None -> 0
  | Some p ->
    let (h, t) = p in
    h + vc_to_lamport t

(* TODO: move to vector clock library *)
let vect_eq vc vc' = vect_leq vc vc' && vect_leq vc' vc

let vect_lt vc vc' = vect_leq vc vc' && (not (vect_eq vc vc'))

type tstamp = vector_clock * int

(* Under the guarantees of causal broadcast, the following defines a total
   order on events. *)
let tstamp_lt (ts1 : tstamp) (ts2 : tstamp)  =
  let (vc1, o1) = ts1 in
  let ts1 = vc_to_lamport vc1 in
  let (vc2, o2) = ts2 in
  let ts2 = vc_to_lamport vc2 in
  (ts1 < ts2 || (ts1 = ts2 && o1 < o2))

let lwwreg_effect (msg : 'valTy writeOpTy msgTy) (reg : 'valTy lwwreg) =
  match reg with
  | None -> Some msg
  | Some reg' ->
    let ((_v, curr_vc), curr_orig) = reg' in
    let curr_ts = (curr_vc, curr_orig) in
    let ((_v', new_vc), new_orig) = msg in
    let new_ts = (new_vc, new_orig) in
    if (tstamp_lt curr_ts new_ts) then Some msg
    else if (tstamp_lt new_ts curr_ts) then reg
    else assert false (* can't happen because of totality of events at the same origin *)

let lwwreg_crdt : ('valTy writeOpTy, 'valTy lwwreg) crdtTy = fun () -> (lwwreg_init_st, lwwreg_effect)

let lwwreg_init (val_ser[@metavar]) (val_deser[@metavar]) addrs rid =
  let initRes = oplib_init val_ser val_deser addrs rid lwwreg_crdt in
  let (get_state, update) = initRes in
  (get_state, update)
