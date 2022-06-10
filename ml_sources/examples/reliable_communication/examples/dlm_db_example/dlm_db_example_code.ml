open !Ast
open Serialization_code
open Dlm_code
open Repdb_code

let do_writes lk wr =
  dlock_acquire lk;
  wr "x" 37;
  wr "y" 1;
  dlock_release lk

let do_reads lk rd  =
  let rec loop () =
    dlock_acquire lk;
    let vx = rd "x" in
    if vx = Some 37
    then
      begin
        let vy = rd "y" in
        assert (vy = Some 1);
        dlock_release lk;
        vy
      end
    else
      begin
        dlock_release lk;
        unsafe (fun () -> Unix.sleepf 2.0);
        loop ()
      end
  in loop ()

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
