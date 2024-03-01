(* open Unix
open Ast
open !Anomalie_code


let ip = (gethostbyname "localhost").h_addr_list.(0)
let srv_addr = makeAddress (string_of_inet_addr ip) 1100
let clt_addr n = makeAddress (string_of_inet_addr ip) (1100 + n)

let runner () =
  if Array.length Sys.argv < 1
  then (prerr_endline "Usage: <node> \n\
                      \ where <node> is in {0-4}"; exit 2);
  (* sendTo_sim_flag := true; *)
  (* set_send_fault_flags 200 700 100; *)
  (* Printf.printf "Press any key to start the node %!"; *)
  (* let _ = read_line () in *)
  let n = int_of_string (Sys.argv.(1)) in
  if n = 0
  then
    (server srv_addr;
     fork (let rec loop () = Unix.sleepf 10.0; loop () in loop ()) ())
  else if n = 1
  then node_init (clt_addr 1) srv_addr
  else if n = 2
  then node_withdraw_ten (clt_addr 2) srv_addr
  else if n = 3
  then node_deposit_twenty (clt_addr 3) srv_addr
  else if n = 4
  then node_check_account (clt_addr 4) (clt_addr 5) srv_addr
  else assert false

let () = runner () *)
