open Ast
open Serialization_code
open Lock_version_code

let node0 clt_addr db_addr () : unit =
  let db_funs = init_client_proxy int_serializer clt_addr db_addr in
  let ((start, commit), (write, _)) = db_funs in
  start (); 
  match write "x" 1 with
  | None -> ()
  | Some () -> 
    match write "y" 1 with
    | None -> ()
    | Some () -> 
      match commit () with
      | None -> ()
      | Some () -> () 

let node1 clt_addr db_addr () : unit =
  let db_funs = init_client_proxy int_serializer clt_addr db_addr in
  let ((start, commit), (write, _)) = db_funs in
  start (); 
  match write "x" 2 with
  | None -> ()
  | Some () -> 
    match write "y" 2 with
    | None -> ()
    | Some () ->
      match commit () with
      | None -> ()
      | Some () -> ()
  
let node2 clt_addr db_addr () : unit =
  let db_funs = init_client_proxy int_serializer clt_addr db_addr in
  let ((start, commit), (_, read)) = db_funs in
  start (); 
  let vx_option = read "x" in
  let vy_option = read "y" in 
  match commit () with
  | None -> ()
  | Some () -> 
    assert (vx_option = vy_option);
    ()

let ip = (Unix.gethostbyname "localhost").h_addr_list.(0)
let server_addr = makeAddress (Unix.string_of_inet_addr ip) 1081
let node0_addr = makeAddress (Unix.string_of_inet_addr ip) 1082
let node1_addr = makeAddress (Unix.string_of_inet_addr ip) 1083
let node2_addr = makeAddress (Unix.string_of_inet_addr ip) 1084

let example () =
  fork (init_server int_serializer server_addr) ();
  fork (node0 node0_addr server_addr) (); 
  fork (node1 node1_addr server_addr) ();
  node2 node2_addr server_addr ();
  ()

let () = Unix.handle_unix_error (example) ()