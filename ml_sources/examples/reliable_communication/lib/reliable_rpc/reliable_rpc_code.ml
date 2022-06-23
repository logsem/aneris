open Ast
open Network_util_code
open Client_server_code
open Map_code
open Serialization_code

type 'a embedding = ('a -> string) * (string -> 'a)
type ('a, 'b) rpc = string * ('a embedding * 'b embedding)
type handler = string * (monitor -> string -> string)
type handler_list = (string, monitor -> string -> string) amap


(* Turns a function and its "RPC spec" into a handler, 
   which is ready to be applied directly on a serialized arg, and to return a serialized response *)
let implement (rpc : ('a, 'b) rpc) f : handler = 
  (fst rpc, (fun mon s_arg -> let arg = (snd (fst (snd rpc))) s_arg in (fst (snd (snd rpc))) (f mon arg)))

(* Applies the right handler according to the name, and returns the serialized response *)
let call_handler (handlers : handler_list) name (s_arg : string) mon =
  let func = unSOME (map_lookup name handlers) in
  func mon s_arg



let service_loop c mon (handlers : handler_list) () : unit =
  let rec loop () =
    let msg = recv c in
    let name = fst msg in
    let s_arg = snd msg in
    monitor_acquire mon;
    let s_resp = call_handler handlers name s_arg mon in
    monitor_release mon;
    send c s_resp;
    loop ()
  in loop ()

let accept_new_connections_loop skt mon handlers () : unit =
  let rec loop () =
    let new_conn = accept skt in
    let (c, _a) = new_conn in
    fork (service_loop c mon handlers) ();
    loop ()
  in loop ()


type name_type = string
type arg_type = string
type req_type = name_type * arg_type
let req_serializer = prod_serializer string_serializer string_serializer

type resp_type = string
let resp_serializer = string_serializer

type chan = (req_type, resp_type) chan_descr * Mutex.t



let init_server_stub addr mon handlers : unit =
  let (skt : (resp_type, req_type) server_skt) = make_server_skt resp_serializer req_serializer addr in
  server_listen skt;
  accept_new_connections_loop skt mon handlers ()

let init_client_stub clt_addr srv_addr : chan = 
  let skt = make_client_skt req_serializer resp_serializer clt_addr in
  let ch = connect skt srv_addr in
  let lk = newlock () in
  (ch, lk)

let call chan rpc arg =
  let ch, lk = chan in
  let s_arg = (fst (fst (snd rpc))) arg in
  let msg = (fst rpc, s_arg) in
  acquire lk;
  send ch msg;
  let s_resp = recv ch in
  release lk;
  (snd (snd (snd rpc))) s_resp
