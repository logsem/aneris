open Ast
open List_code
open Network_util_code

type 'stTy mergeFnTy = 'stTy -> 'stTy -> 'stTy

type ('opTy, 'stTy) mutatorFnTy = int -> 'stTy -> 'opTy -> 'stTy

type 'a stateRef = 'a Atomic.t

type ('opTy, 'stTy) crdtTy = (('stTy * ('opTy, 'stTy) mutatorFnTy) * 'stTy mergeFnTy)

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
let apply (deser_st[@metavar]: 'stTy stDeserTy)
    lk sh (st : 'stTy stateRef) (merge : 'stTy mergeFnTy) : unit =
  loop_forever
    (fun () ->
       acquire lk;
       let msg = unSOME (receiveFrom sh) in
       let st' = deser_st (fst msg) in
       st := merge !st st';
       release lk)

(* Mutates the current state of the CRDT.
   Partially applied and called by the user as `update op`. *)
let update lk (mut : ('opTy,'stTy) mutatorFnTy)
    (st : 'stTy stateRef) (op : 'opTy) i =
  acquire lk; st := mut i !st op; release lk


let sendToAll sh msg dstl i =
  let rec aux j =
    if j < list_length dstl then
      if i = j then aux (j + 1)
      else
        begin
          let dst = unSOME (list_nth dstl j) in
          ignore(sendTo sh msg dst);
          aux (j + 1)
        end
    else ()
  in aux 0

let broadcast (ser_st[@metavar "val"]: 'stTy stSerTy)
    lk sh st dstl i =
  let rec loop () =
    unsafe (fun () -> Unix.sleepf 2.0);
    acquire lk;
    let s = !st in
    release lk;
    let msg = ser_st s in
    sendToAll sh msg dstl i;
    loop ()
  in loop ()

let statelib_init
    (st_ser[@metavar "val"] : 'stTy stSerTy)
    (st_deser[@metavar "val"] : 'stTy stDeserTy)
    (addrlst : saddr alist)
    (rid : int)
    (crdt : ('opTy, 'stTy) crdtTy) =
  let ((init_st, mut), merge) = crdt in
  let st = ref init_st in
  let lk = newlock () in
  let sh = socket PF_INET SOCK_DGRAM IPPROTO_UDP in
  let addr = unSOME (list_nth addrlst rid) in
  socketBind sh addr;
  fork (apply st_deser lk sh st) merge;
  fork (broadcast st_ser lk sh st addrlst) rid;
  let get = get_state lk st in
  let upd = update lk mut st rid in
  (get, upd)
