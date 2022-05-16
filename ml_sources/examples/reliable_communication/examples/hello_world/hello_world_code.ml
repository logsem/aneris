open !Ast
open Client_server_code
open Serialization_code

let server srv_addr =
  let skt = make_server_skt
      string_serializer
      string_serializer
      srv_addr in
  server_listen skt;
  let new_conn = accept skt in
  let (c, _clt_addr) = new_conn in
  let (req : string) = recv c in
  send c req


let client clt_addr srv_addr =
  let skt = make_client_skt
      string_serializer
      string_serializer
      clt_addr in
  let ch = connect skt srv_addr in
  send ch "Hello World!"
