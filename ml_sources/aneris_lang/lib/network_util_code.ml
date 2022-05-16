open Ast
open List_code
open Set_code

let unSOME o = match o with
    None -> assert false
  | Some x -> x

let sendto_all skt ns msg =
  list_iter (fun n -> ignore(sendTo skt msg n)) ns

let rec listen skt handler =
  match receiveFrom skt with
  | Some m ->
     let msg = fst m in
     let sender = snd m in
     handler msg sender
  | None -> listen skt handler

let wait_receivefrom skt test =
  let rec loop () =
     let msg = unSOME (receiveFrom skt) in
     if test msg then msg else loop () in
  loop ()

let sendto_all_set =
  fun skt x msg ->
  set_iter (fun n -> let _l = sendTo skt msg n in ()) x

let receivefrom_all =
  fun skt nodes ->
  let rec recv n =
    let msg = unSOME (receiveFrom skt) in
    let sender = snd msg in
    if sender = n then (fst msg)
    else recv n in
  list_fold  (fun acc n -> list_append acc (list_cons (recv n) list_nil)) list_nil nodes

let wait_receivefrom_all =
  fun skt nodes test ->
  let rec recv n =
    let msg = unSOME (receiveFrom skt) in
    let sender = snd msg in
    let m = fst msg in
    if (sender = n) && (test m) then m
    else recv n in
  list_fold  (fun acc n -> list_append acc (list_cons (recv n) list_nil)) list_nil nodes

let tag_of_message msg =
  match findFrom msg 0 '_' with
    Some i  -> substring msg 0 i
  | None -> "UNDEFINED"

let value_of_message msg =
  match findFrom msg 0 '_' with
    Some i  -> let length = strlen msg in
               let start  = i + 1 in
               substring msg start (length - start)
  | None -> "UNDEFINED"
