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
  let (clt_c, _clt_addr) = new_conn in
  let (req : string) = recv clt_c in
  send clt_c req


let client clt_addr0 clt_addr1 srv_addr0 srv_addr1 =
  let skt0 = make_client_skt string_serializer string_serializer clt_addr0 in
  let skt1 = make_client_skt string_serializer string_serializer clt_addr1 in
  let ch0 = connect skt0 srv_addr0 in
  let ch1 = connect skt1 srv_addr1 in
  send ch0 "Hello World, Server 0!";
  send ch1 "Hello World, Server 1!"
