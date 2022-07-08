(* Path : cd Documents/aneris/ml_sources/_build/default/examples/reliable_communication/examples/reference_rpc/ *)

open Reliable_rpc_code
open Serialization_code
open Unix
open Ast
open List_code

let put' r n = r := n
let incr' r () = r := !r + 1
let show' r () = !r

let put, incr, show = let r = ref 0 in (
  put' r,
  incr' r,
)

let unit_embedding = (unit_serializer.s_ser, unit_serializer.s_deser)
let int_embedding = (int_serializer.s_ser, int_serializer.s_deser)

let put_RPC = ("put", (int_embedding, unit_embedding))
let incr_RPC = ("incr", (unit_embedding, unit_embedding))
let show_RPC = ("show", (unit_embedding, int_embedding))

let handlers : handler alist = list_cons (implement put_RPC put) (list_cons (implement incr_RPC incr) (list_cons (implement show_RPC show) list_nil))
(* let handlers : handler alist = [ implement put_RPC put; implement incr_RPC incr; implement show_RPC show ] *)



let server srv = 
  init_server_stub srv handlers

let client clt srv =
  let chan = init_client_stub clt srv in
  let put = call chan put_RPC in
  let incr = call chan incr_RPC in
  let show = call chan show_RPC in

  Printf.printf "%d\n%!" (show ());
  incr ();
  Printf.printf "%d\n%!" (show ());
  put 4;
  Printf.printf "%d\n%!" (show ())

let client2 clt srv =
  let chan = init_client_stub clt srv in
  let incr = call chan incr_RPC in
  let show = call chan show_RPC in

  Printf.printf "%d\n%!" (show ());
  incr ();
  Printf.printf "%d\n%!" (show ())



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
      | "clt2" ->
        Printf.printf "Coucou2\n%!";
        client2 clt2_saddr srv_saddr;
        Printf.printf "Assertion succeeded!\n%!";
        monitor_send_faults ()
      | "srv" ->
        server srv_saddr
      |  _    -> assert false
    in ()
  
  let () = runner ()
  
