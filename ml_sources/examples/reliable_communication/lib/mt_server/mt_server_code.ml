open Ast
open Client_server_code

(** Generic methods for multi-threaded server with monitored requests. *)

(** Serve requests on the the channel `c` via monitored queue of events. *)
let service_loop c mon (request_handler : monitor -> 'req -> 'rep) () : unit =
  let rec loop () =
    let req = recv c in
    let rep = request_handler mon req in
    send c rep;
    loop ()
  in loop ()

let accept_new_connections_loop skt mon request_handler () : unit =
  let rec loop () =
    let new_conn = accept skt in
    let (c, _a) = new_conn in
    fork (service_loop c mon request_handler) ();
    loop ()
  in loop ()

let run_server
    (ser[@metavar] : 'repl serializer)
    (deser[@metavar] : 'req serializer) addr mon
    (request_handler : monitor -> 'req -> 'rep) : unit  =
  let (skt :  ('repl, 'req) server_skt) = make_server_skt ser deser addr in
  server_listen skt;
  fork (accept_new_connections_loop skt mon request_handler) ()

let make_request (ch :  ('req, 'repl) chan_descr) (lk : Mutex.t) (req : 'req) : 'repl =
  acquire lk;
  send ch req;
  let msg = recv ch in
  release lk;
  msg

let init_client_proxy
    (ser[@metavar] : 'req serializer) (deser[@metavar] : 'repl serializer)
    clt_addr srv_addr : 'req -> 'repl =
  let skt = make_client_skt ser deser clt_addr in
  let ch = connect skt srv_addr in
  let lk = newlock () in
  make_request ch lk
