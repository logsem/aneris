open Ast
open List_code
open Vector_clock_code
open Rcb_code (* TODO: needed for loop_forever. Remove. *)

(* A simple library for implementing op-based CRDTs.
   See `oplib_init` for details. *)

(* Ideally some of the type constructors below would be
   algebraic data types, but we don't have those in AnerisLang. *)

type repIdTy = int                               (* replica id *)
type 'opTy msgTy = ('opTy * vector_clock) * repIdTy (* a message is an operation tagged with a vc
                                                    and the id of the originating node *)
type 'a broadcastFnTy = 'a -> 'a msgTy      (* broadcast function (RCB) *)
type 'a deliverFnTy = unit -> 'a msgTy option    (* deliver function (RCB) *)
(* effect function (passed by the CRDT implementor)
   effect takes an operation and a CRDT state, and returns the new state
   that results from applying the operation *)
type ('opTy, 'stateTy) effectFnTy = 'opTy msgTy -> 'stateTy -> 'stateTy

type 'a stateRef = 'a Atomic.t

(* The type constructor for op-based CRDTs.
   An op-based CRDT is a pair `(initSt, effectFn)` where
   - `initSt` is the initial CRDT state
   - `effectFn` is CRDT's effector *)
type ('opTy, 'stateTy) crdtTy = unit -> (unit -> 'stateTy) * ('opTy, 'stateTy) effectFnTy

type 'opTy opSerTy = 'opTy -> string
type 'opTy opDeserTy = string -> 'opTy

(* Returns a copy of the current state of the CRDT.
   Partially applied, and called by the user as
   `get_state ()`. *)
let get_state lock (st : 'stateTy stateRef) () =
  acquire lock;
  let res = !st in
  release lock;
  res

(* The apply thread perpetually loops and tries to deliver operations from
   other nodes, calling `effect` to apply the operations if they exist. *)
let apply_thread lock (deliver : 'opTy deliverFnTy)(st : 'stateTy stateRef) (effect : ('opTy, 'stateTy) effectFnTy) =
  loop_forever (fun () ->
      acquire lock;
      begin
        match (deliver ()) with
          Some msg ->
            st := effect msg !st
        | None -> ()
      end;
      release lock;)

(* Mutates the current state of the CRDT.
   Partially applied and called by the user as
   `update op`. *)
let update lock (broadcast : 'opTy broadcastFnTy) (st : 'stateTy stateRef)
           (effect : ('opTy, 'stateTy) effectFnTy) (op : 'opTy) =
  acquire lock;
  (* Since RCB doesn't broadcast to ourselves, we have
     to manually run the update right now. *)
  let msg = broadcast op in
  st := effect msg !st;
  release lock

(* Initializes the CRDT.
   - `broadcast`: a function that sends a message to all nodes except the current one.
   - `deliver`: a function that delivers the next message in causal order, if one exists.
   - `crdt`: the CRDT implementation.

  Returns a pair (get_state, update) of functions.
  - `get_state` returns (a copy of) the current state of the CRDT.
  - `update` mutates the current CRDT state according to a new operation.
    It also broadcasts the operation to all other nodes. *)
  let oplib_init (op_ser[@metavar] : 'opTy opSerTy) (op_deser[@metavar] : 'opTy opDeserTy)
                 (addrs : saddr alist) (rid : repIdTy)
                 (crdt : ('opTy, 'stateTy) crdtTy) =
    let rcbInitRes = rcb_init op_ser op_deser addrs rid in
    let (deliver, broadcast) = rcbInitRes in
    let crdt_res = crdt () in
    let (init_st, effect) = crdt_res in
    let st = ref (init_st ()) in
    let lock = newlock () in
    fork (apply_thread lock deliver st) effect;
    (get_state lock st, update lock broadcast st effect)
