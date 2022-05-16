open !Ast
open Serialization_code
open Dlm_code
open Ddb_code

let do_transaction lk wr =
  dlock_acquire lk;
  wr "x" 1;
  wr "y" 37;
  dlock_release lk

let repeat_read_until lk rd k v =
  let rec loop () =
    dlock_acquire lk;
    let res = rd k in
    dlock_release lk;
    if res = Some v
    then ()
    else begin
      unsafe (fun () -> Unix.sleepf 2.0); loop ()
    end
  in loop ()

let do_read lk rd =
  ignore (repeat_read_until lk rd "x" 1);
  dlock_acquire lk;
  let vy = rd "y" in
  dlock_release lk;
  assert (vy = Some 37)

let node0 clt_addr00 clt_addr01 dlock_srv_addr db_srv_addr =
  let lk_chan = dlock_subscribe_client clt_addr00 dlock_srv_addr in
  let db_funs = install_proxy int_serializer clt_addr01 db_srv_addr in
  let (wr, _rd) = db_funs in
  do_transaction lk_chan wr

let node1 clt_addr10 clt_addr11 dlock_srv_addr db_srv_addr =
  let lk_chan = dlock_subscribe_client clt_addr10 dlock_srv_addr in
  let db_funs = install_proxy int_serializer clt_addr11 db_srv_addr in
  let (_wr, rd) = db_funs in
  do_read lk_chan rd
