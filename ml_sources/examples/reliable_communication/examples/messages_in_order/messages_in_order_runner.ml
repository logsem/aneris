open Unix
open Ast
open Messages_in_order_code

let monitor_send_faults () =
  let loop () =
    while true do
      Unix.sleepf 1.0;
      print_send_faults ();
    done in
  ignore (Thread.create loop ())

let ip = (gethostbyname "localhost").h_addr_list.(0)
let clt_saddr = makeAddress (string_of_inet_addr ip) 1100
let srv_saddr = makeAddress (string_of_inet_addr ip) 1101

let runner () =
  if Array.length Sys.argv < 2
  then (prerr_endline "Usage: <node> \n\
                      \ where <node> is in {clt srv}"; exit 2);
  sendTo_sim_flag := true;
  set_send_fault_flags 300 600 100;
  Printf.printf "Press any key to start the node %!";
  let _ = read_line () in
  let _ =
    match Sys.argv.(1) with
    | "clt" ->
      client clt_saddr srv_saddr;
      Printf.printf "Assertion succeeded!\n%!";
      monitor_send_faults ();
      fork (let rec loop () = Unix.sleepf 10.0; loop () in loop ()) ()
    | "srv" ->
      server srv_saddr;
      monitor_send_faults ();
      fork (let rec loop () = Unix.sleepf 10.0; loop () in loop ()) ()

    |  _    -> assert false
  in ()

let () = runner ()
