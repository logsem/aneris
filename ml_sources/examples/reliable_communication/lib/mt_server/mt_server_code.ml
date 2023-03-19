open Ast
open Client_server_code

type ('a, 'b) rpc = ('a, 'b) chan_descr

let try_recv_timeout (c : ('a, 'b) rpc) =
  let rec aux n =
    let reqo = try_recv c in
    if reqo = None
    then begin Unix.sleepf 0.1; aux (n-1) end
    else reqo
  in aux 100

let service_loop_opt c (request_handler : 'req option -> 'repl option) () : unit =
  let rec loop () =
    let req = try_recv_timeout c in
    let rep = request_handler req in
    begin
      match rep with
      | None -> ()
      | Some rep -> send c rep
    end;
    loop ()
  in loop ()

let accept_new_connections_loop_opt skt request_handler () : unit =
  let rec loop () =
    let new_conn = accept skt in
    let (c, _a) = new_conn in
    fork (service_loop_opt c request_handler) ();
    loop ()
  in loop ()

let run_server_opt
    (ser[@metavar] : 'repl serializer)
    (deser[@metavar] : 'req serializer)
    addr
    (request_handler : 'req option -> 'repl option) : unit  =
  let (skt :  ('repl, 'req) server_skt) = make_server_skt ser deser addr in
  server_listen skt;
  fork (accept_new_connections_loop_opt skt request_handler) ()

let service_loop c (request_handler : 'req -> 'repl) () : unit =
  let rec loop () =
    let req = recv c in
    let rep = request_handler req in
    send c rep;
    loop ()
  in loop ()

let accept_new_connections_loop skt (request_handler : 'req -> 'repl) () : unit =
  let rec loop () =
    let new_conn = accept skt in
    let (c, _a) = new_conn in
    fork (service_loop c request_handler) ();
    loop ()
  in loop ()

let run_server
    (ser[@metavar] : 'repl serializer)
    (deser[@metavar] : 'req serializer)
    addr
    (request_handler : 'req -> 'repl) : unit  =
  let (skt :  ('repl, 'req) server_skt) = make_server_skt ser deser addr in
  server_listen skt;
  fork (accept_new_connections_loop skt request_handler) ()

let make_request (ch :  ('req, 'repl) chan_descr) : 'req -> 'repl =
  fun req ->
  send ch req;
  recv ch

let init_client_proxy
    (ser[@metavar] : 'req serializer) (deser[@metavar] : 'repl serializer)
    clt_addr srv_addr : ('a, 'b) rpc =
  let skt = make_client_skt ser deser clt_addr in
  let ch = connect skt srv_addr in
  ch
