open !Ast
open Serialization_code
open Network_util_code
open Snapshot_isolation_code
open Util_code

let tbody_init (s : int connection_state) : unit =
  write s "x" 1; write s "y" 1; write s "s0" 1

let wait_s0 (s : int connection_state) =
  wait_on_key s (fun v -> v = 1) "s0"

let tbody_xy (s : int connection_state) : unit =
  wait_s0 s;
  let n = unSOME (read s "x") in
  if 0 < n then
    begin
      write s "y" (-1);
      write s "s1" 1;
      unsafe (fun () -> Printf.printf "Set y to -1 \n%!");
      unsafe (fun () -> Unix.sleepf 0.5);
    end
  else ()


let tbody_yx (s : int connection_state) : unit =
  wait_s0 s;
  let n = unSOME (read s "y") in
  if 0 < n then
    begin
      write s "x" (-1);
      write s "s2" 1;
      unsafe (fun () -> Printf.printf "Set x to -1 \n%!");
      unsafe (fun () -> Unix.sleepf 0.5);
    end
  else ()

let tbody_read (s : int connection_state) : unit =
  unsafe (fun () ->
      Random.self_init ();
      let r = Random.int 5 in
      Printf.printf "%d\n%!" r;
      Unix.sleep r);
  wait_s0 s;
  let n1 = unSOME (read s "x") in
  let n2 = unSOME (read s "y") in
  let vs1 = read s "s1" in
  let vs2 = read s "s2" in
  let b = (0 <= (n1 + n2)) in
  let _check =
    if (vs1 = Some 1 && vs2 = Some 1) then assert (not b)
    else (assert b) in
  unsafe (fun () -> Printf.printf "(x,y) = (%d, %d) \n%!" n1 n2)

let node_init caddr kvs_addr =
  run_client caddr kvs_addr tbody_init

let node_xy caddr kvs_addr =
  run_client caddr kvs_addr tbody_xy

let node_yx caddr kvs_addr =
  run_client caddr kvs_addr tbody_yx

let node_read caddr kvs_addr =
    run_client caddr kvs_addr tbody_read

let server srv =
  unsafe (fun () -> Printf.printf "Start server.\n%!");
  init_server int_serializer srv;
  unsafe (fun () -> Printf.printf "Server started.\n%!")
