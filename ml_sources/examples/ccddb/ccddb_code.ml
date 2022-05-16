open Ast
open List_code
open Network_util_code
open Vector_clock_code
open Serialization_code
open Map_code

(* We follow the following variable naming convention:

     - [db]    : a reference to the local database
     - [t]     : a reference to the local time (vector clock)
     - [m]     : tuple (origin, key, value) where origin is the id of
                 the node that caused the event
     - [msg]   : tuple (origin, key, value, timestamp)
     - [t, s]  : timestamp (vector clock)
     - [nodes] : list of ips of other nodes
   *)

let store_update db t m =
  let (((key, value), _vc), origin) = m in
  t := vect_inc !t origin;
  db := map_insert key value !db

let store_test t i =
  let l = list_length t in
  fun w ->
    let s = snd (fst w) in (* timestamp of event *)
    let j = snd w in       (* origin *)
    if i = j then
      false
    else
    if j < l then
      vect_applicable s t j
    else
      false

let store_apply db t lock inQueue i =
  let rec apply () =
    acquire lock;
    let x = list_find_remove (store_test (!t) i) !inQueue in
    begin
      match x with
        Some a ->
          let msg = fst a in
          let rest = snd a in
          inQueue := rest;
          store_update db t msg
      | None -> ()
    end;
    release lock;
    apply () in
  apply ()

let write_event_ser (val_ser[@metavar]) =
  prod_ser (prod_ser (prod_ser string_ser val_ser) vect_serialize) int_ser

let write_event_deser (val_deser[@metavar]) =
  prod_deser
    (prod_deser
       (prod_deser string_deser val_deser)
       vect_deserialize)
    int_deser

let send_thread (val_ser[@metavar]) i socket_handler lock nodes outQueue =
  let rec out () =
    acquire lock;
    let tmp = !outQueue in
    if not (list_is_empty tmp)
    then
      begin
        outQueue := list_tail tmp;
        release lock;
        let we = unSOME (list_head tmp) in
        let msg = write_event_ser val_ser we in
        let rec send j =
          if j < list_length nodes then
            if i = j then
              send (j + 1)
            else
              let n = unSOME (list_nth nodes j) in
              ignore(sendTo socket_handler msg n);
              send (j + 1)
          else ()
        in
        send 0;
        out ()
      end
    else
      begin
        release lock;
        out ()
      end
  in out ()

let recv_thread (val_deser[@metavar]) socket_handler lock inQueue =
  let rec loop () =
    let msg = fst (unSOME (receiveFrom socket_handler)) in
    acquire lock;
    let we = write_event_deser val_deser msg in
    inQueue := list_cons we (!inQueue);
    release lock;
    loop ()
  in loop ()

let store_read db lock key =
  acquire lock;
  let r = map_lookup key !db in
  release lock; r

let store_write db t outQueue lock i key value =
  acquire lock;
  t := vect_inc !t i;
  db := map_insert key value !db;
  outQueue := list_cons (((key, value), !t), i) (!outQueue);
  release lock

(* Node [i] with list of addresses [addrlst] *)
let ccddb_init (val_ser[@metavar]) (val_deser[@metavar]) addrlst i =
  let db = ref (map_empty ()) in
  let n = list_length addrlst in
  let t = ref (vect_make n 0) in
  let inQueue = ref list_nil in
  let outQueue = ref list_nil in
  let lock = newlock () in
  let socket_handler = socket PF_INET SOCK_DGRAM IPPROTO_UDP in
  let addr = unSOME (list_nth addrlst i) in
  socketBind socket_handler addr;
  fork (store_apply db t lock inQueue) i;
  fork (send_thread val_ser i socket_handler lock addrlst) outQueue;
  fork (recv_thread val_deser socket_handler lock) inQueue;
  (store_read db lock, store_write db t outQueue lock i)
