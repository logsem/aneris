open Ast
open List_code
open Network_util_code

type 'stTy mergeFnTy = 'stTy -> 'stTy -> 'stTy

type ('opTy, 'stTy) mutatorFnTy = int -> 'stTy -> 'opTy -> 'stTy

type 'a stateRef = 'a Atomic.t

type ('opTy, 'stTy) crdtTy = unit -> (((unit -> 'stTy) * ('opTy, 'stTy) mutatorFnTy) * 'stTy mergeFnTy)

type 'stTy stSerTy = 'stTy -> string
type 'stTy stDeserTy = string -> 'stTy

(* Returns a copy of the current state of the CRDT.
   Partially applied, and called by the user as `get_state ()`. *)
let get_state lock (st : 'stTy stateRef) () =
  acquire lock;
  let res = !st in
  release lock;
  res

(* TODO: remove and factor out with rcb_code.ml *)
let rec loop_forever thunk =
  thunk ();
  loop_forever thunk

(* The apply thread perpetually loops and tries to fetch the state from
   other nodes, merging it with the replica's own state. *)
let apply_thread (deser_st[@metavar]: 'stTy stDeserTy)
    lk sh (st : 'stTy stateRef) (merge : 'stTy mergeFnTy) : unit =
  loop_forever
    (fun () ->
       let msg = unSOME (receiveFrom sh) in
       let st' = deser_st (fst msg) in
       acquire lk;
       st := merge !st st';
       release lk)

(* Mutates the current state of the CRDT.
   Partially applied and called by the user as `update op`. *)
let update lk (mut : ('opTy,'stTy) mutatorFnTy)
    i (st : 'stTy stateRef) (op : 'opTy) =
  acquire lk; st := mut i !st op; release lk


let sendToAll sh (dstl : saddr alist) i msg =
  let j = ref 0 in
  let rec aux () =
    if !j < list_length dstl then
      if i = !j then (j := !j + 1; aux ())
      else
        begin
          let dst = unSOME (list_nth dstl !j) in
          ignore(sendTo sh msg dst);
          j := !j + 1;
          aux ()
        end
    else ()
  in aux ()

let broadcast (ser_st[@metavar "val"]: 'stTy stSerTy)
    lk sh st dstl i =
  loop_forever(
    fun () ->
    unsafe (fun () -> Unix.sleepf 2.0);
    acquire lk;
    let s = !st in
    release lk;
    let msg = ser_st s in
    sendToAll sh dstl i msg)

let statelib_init
    (st_ser[@metavar "val"] : 'stTy stSerTy)
    (st_deser[@metavar "val"] : 'stTy stDeserTy)
    (addrlst : saddr alist)
    (rid : int)
    (crdt : ('opTy, 'stTy) crdtTy) =
  let init_st_crdt = crdt () in
  let ((init_st, mut), merge) = init_st_crdt in
  let st = ref (init_st ()) in
  let lk = newlock () in
  let sh = socket PF_INET SOCK_DGRAM IPPROTO_UDP in
  let addr = unSOME (list_nth addrlst rid) in
  socketBind sh addr;
  fork (apply_thread st_deser lk sh st) merge;
  fork (broadcast st_ser lk sh st addrlst) rid;
  let get = get_state lk st in
  let upd = update lk mut rid st in
  (get, upd)
