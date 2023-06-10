open !Ast
open Serialization_code
open Snapshot_isolation_code

let run_client caddr kvs_addr tbody =
  unsafe (fun () -> Printf.printf "Start client.\n%!");
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  unsafe (fun () -> Printf.printf "Client started.\n%!");
  let b = run cst tbody in
  unsafe (fun () -> Printf.printf "Transaction %s.\n%!"
             (if b then "committed" else "aborted"))


let tbody_init (s : int connection_state) : unit =
  write s "x" 1; write s "y" 1; write s "s0" 1

let rec wait_s0 (s : int connection_state) =
  match read s "s0" with
  | None ->
    let _b = commit s in
    start s; wait_s0 s
  | Some v ->
    if v = 1
    then (let _b = commit s in start s)
    else
      let _b = commit s in
      start s; wait_s0 s

let tbody_xy (s : int connection_state) : unit =
  wait_s0 s;
  match read s "x" with
  | None -> assert false;
  | Some n ->
    if 0 < n then
      begin
        write s "y" (-1);
        write s "s1" 1;
        unsafe (fun () -> Printf.printf "Set y to -1 \n%!");
        (* unsafe (fun () -> Unix.sleepf 0.5); *)
      end
    else ()

let tbody_yx (s : int connection_state) : unit =
  wait_s0 s;
  match read s "y" with
  | None -> assert false;
  | Some n ->
    if 0 < n then
      begin
        write s "x" (-1);
        write s "s2" 1;
        unsafe (fun () -> Printf.printf "Set x to -1 \n%!");
        (* unsafe (fun () -> Unix.sleepf 0.5); *)
      end
    else ()

let tbody_read (s : int connection_state) : unit =
  wait_s0 s;
  unsafe (fun () -> Unix.sleepf 2.0);
  let vx = read s "x" in
  let vy = read s "y" in
  match vx with
  | Some n1 ->
    begin match vy with
      | Some n2 ->
        let vs1 = read s "s1" in
        let vs2 = read s "s2" in
        unsafe (fun () -> Printf.printf "(x,y) = (%d, %d) \n%!" n1 n2);
        let b = 0 <= (n1 + n2) in
        if (vs1 = Some 1 && vs2 = Some 1)
        then assert (not b)
        else (assert b);
      | None -> assert false
    end
  | None -> assert false

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
