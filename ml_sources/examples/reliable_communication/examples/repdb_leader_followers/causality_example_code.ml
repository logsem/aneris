open !Ast
open Serialization_code
open Repdb_code

let do_writes wr =
  wr "x" 37;
  wr "y" 1

let wait_on_read rd k v =
  let rec loop () =
    let res = rd k in
    if res = Some v
    then ()
    else (unsafe (fun () -> Unix.sleepf 2.0); loop ())
  in loop ()

let do_reads rd =
  wait_on_read rd "y" 1;
  let vx = rd "x" in
  assert (vx = Some 37)

let node0 clt_addr0 db_laddr =
  let db_funs = init_client_leader_proxy int_serializer clt_addr0 db_laddr in
  let (wr, _rd) = db_funs in
  do_writes wr

let node1 clt_addr1 faddr =
  let rd = init_client_follower_proxy int_serializer clt_addr1 faddr in
  do_reads rd
