open Ast
open List_code
open Set_code
open Map_code
open Network_util_code


let receivefrom_nodup rcvlog skt =
  let rec loop () =
     let msg = unSOME (receiveFrom skt) in
     if set_mem msg rcvlog then loop ()
     else (msg, set_add msg rcvlog) in
  loop ()

let rec receivefrom_nodup_n skt msgs n =
  if n = 0 then (list_nil, msgs) else
    let tmp = receivefrom_nodup msgs skt in
    let m = fst tmp in
    let msgs' = snd tmp in
    let tailmsgs = receivefrom_nodup_n skt msgs' (n - 1) in
    let ms = fst tailmsgs in
    let msgs'' = snd tailmsgs in
    (list_cons m ms, msgs'')

let nodup_empty = set_empty

let nodup_init () =
  let log = ref (nodup_empty ()) in
  fun skt ->
  let tmp = receivefrom_nodup !log skt in
  let msg  = fst tmp in
  let log' = snd tmp in
  log := log';
  msg

let receivefrom_nodup_set skt rcv addrs =
  let msgs = ref (map_empty ()) in
  let rec loop () =
     if set_equal (map_dom !msgs) addrs then !msgs
     else
       let msg = rcv skt in
       msgs := map_insert (snd msg) (fst msg) !msgs;
       loop () in
   loop ()
