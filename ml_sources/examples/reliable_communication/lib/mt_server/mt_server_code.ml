open Ast
open Client_server_code


type ('a, 'b) rcb = ('a, 'b) chan_descr


let service_loop c (request_handler : 'req -> 'rep) () : unit =
  let rec loop () =
    let req = recv c in
    let rep = request_handler req in
    send c rep;
    loop ()
  in loop ()

let accept_new_connections_loop skt request_handler () : unit =
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
    (request_handler : 'req -> 'rep) : unit  =
  let (skt :  ('repl, 'req) server_skt) = make_server_skt ser deser addr in
  server_listen skt;
  fork (accept_new_connections_loop skt request_handler) ()

let make_request (ch :  ('req, 'repl) chan_descr) : 'req -> 'repl =
  fun req ->
  send ch req;
  recv ch

let init_client_proxy
    (ser[@metavar] : 'req serializer) (deser[@metavar] : 'repl serializer)
    clt_addr srv_addr : ('a, 'b) rcb =
  let skt = make_client_skt ser deser clt_addr in
  let ch = connect skt srv_addr in
  ch
