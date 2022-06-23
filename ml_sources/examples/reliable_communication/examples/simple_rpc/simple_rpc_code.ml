(* Path : cd Bureau/aneris/ml_sources/_build/default/examples/reliable_communication/examples/simple_rpc/ *)

open Reliable_rpc_code
open Serialization_code
open Unix
open Ast
open List_code


(* Setup of the RPC *)

let add mon (a, b) = ignore mon; a + b

let sub mon (a, b) = ignore mon; a - b

let nothing mon () = ignore mon

let incr mon a = ignore mon; a + 1

let op_serializer = prod_serializer int_serializer int_serializer
let unit_embedding = (unit_serializer.s_ser, unit_serializer.s_deser)
let int_embedding = (int_serializer.s_ser, int_serializer.s_deser)
let op_embedding = (op_serializer.s_ser, op_serializer.s_deser)

let add_RPC = ("add", (op_embedding, int_embedding))
let sub_RPC = ("sub", (op_embedding, int_embedding))
let incr_RPC = ("incr", (int_embedding, int_embedding))

let nothing_RPC = ("nothing", (unit_embedding, unit_embedding))

let op_handlers : handler alist = list_cons (implement add_RPC add) (list_cons (implement sub_RPC sub) (list_cons (implement incr_RPC incr) list_nil))
let nothing_handlers : handler alist = list_cons (implement nothing_RPC nothing) list_nil
  
(* let op_handlers : handler alist = [ implement add_RPC add; implement sub_RPC sub; implement incr_RPC incr ] *)


(* Codes of server and client *)

let server srv = 
  let mon = new_monitor () in
init_server_stub srv mon op_handlers

let client clt srv = 
  let chan = init_client_stub clt srv in
  Printf.printf "%d\n%!" (call chan incr_RPC 37);
  Printf.printf "%d\n%!" (call chan sub_RPC (54, 28));
  Printf.printf "%d\n%!" (call chan add_RPC (1, 3))
  

(*let client2 clt srv =
  let obj = init_client_proxy clt srv in
  Printf.printf "%d\n%!" (obj#call sub_RPC (50, 1));
  Printf.printf "%d\n%!" (obj#call add_RPC (1, 1));
  Printf.printf "%d\n%!" (obj#call incr_RPC 101)*)


(* Technicalities *)

let monitor_send_faults () =
  let loop () =
    while true do
      Unix.sleepf 1.0;
      print_send_faults ();
    done in
  ignore (Thread.create loop ())

let ip = (gethostbyname "localhost").h_addr_list.(0)
let clt_saddr = makeAddress (string_of_inet_addr ip) 1100
let clt2_saddr = makeAddress (string_of_inet_addr ip) 1102
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
      Printf.printf "Coucou\n%!";
      client clt_saddr srv_saddr;
      Printf.printf "Assertion succeeded!\n%!";
      monitor_send_faults ()
    (*| "clt2" ->
      Printf.printf "Coucou2\n%!";
      client2 clt2_saddr srv_saddr;
      Printf.printf "Assertion succeeded!\n%!";
      monitor_send_faults ()*)
    | "srv" ->
      server srv_saddr
    |  _    -> assert false
  in ()

let () = runner ()

