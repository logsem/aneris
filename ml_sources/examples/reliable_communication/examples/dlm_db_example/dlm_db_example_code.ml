open !Ast
open Serialization_code
open Dlm_code
open Repdb_code

let do_writes lk wr =
  dlock_acquire lk;
  wr "x" 37;
  wr "y" 1;
  dlock_release lk

let dl_wait_on_read lk rd k v =
  let rec loop () =
    dlock_acquire lk;
    let res = rd k in
    dlock_release lk;
    if res = Some v
    then ()
    else (unsafe (fun () -> Unix.sleepf 2.0); loop ())
  in loop ()

let do_reads lk rd =
  dl_wait_on_read lk rd "x" 37;
  dlock_acquire lk;
  let vy = rd "y" in
  dlock_release lk;
  assert (vy = Some 1)

let node0 clt_addr00 clt_addr01 dl_addr db_laddr =
  let lk_chan = dlock_subscribe_client clt_addr00 dl_addr in
  let db_funs = init_client_leader_proxy int_serializer clt_addr01 db_laddr in
  let (wr, _rd) = db_funs in
  do_writes lk_chan wr

let node1 clt_addr10 clt_addr11 dl_addr db_laddr =
  let lk_chan = dlock_subscribe_client clt_addr10 dl_addr in
  let db_funs = init_client_leader_proxy int_serializer clt_addr11 db_laddr in
  let (_wr, rd) = db_funs in
  do_reads lk_chan rd
