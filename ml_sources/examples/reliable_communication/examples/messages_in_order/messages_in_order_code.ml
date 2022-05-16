open !Ast
open Serialization_code
open Client_server_code

let server srv =
  unsafe (fun () -> Printf.printf "Install server.\n%!");
  unsafe (fun () -> Printf.printf "Creating socket.\n%!");
  let s = make_server_skt int_serializer int_serializer srv in
  unsafe (fun () -> Printf.printf "Start listening.\n%!");
  server_listen s;
  let new_conn = accept s in
  let (c, _clt) = new_conn in
  let _r1 = let m = recv c in send c m in
  let _r2 = let m = recv c in send c m in
  let _r3 = let m = recv c in send c m in
  ()

let client clt srv =
  unsafe (fun () -> Printf.printf "Install client.\n%!");
  unsafe (fun () -> Printf.printf "Creating socket.\n%!");
  let s = make_client_skt int_serializer int_serializer clt in
  unsafe (fun () -> Printf.printf "Connecting to the server.\n%!");
  let c = connect s srv in
  send c 1;
  send c 2;
  send c 3;
  let m1 = recv c in
  let m2 = recv c in
  let m3 = recv c in
  assert (m1 = 1 && m2 = 2 && m3 = 3);


(*
let server srv =
  let s = make_server_skt int_serializer int_serializer srv in
  server_listen s;
  let new_conn = accept s in
  let (c, _clt) = new_conn in
  let _r1 = let m = recv c in send c m in
  let _r2 = let m = recv c in send c m in
  let _r1 = let m = recv c in send c m in
  ()

let client clt srv =
  let s = make_client_skt int_serializer int_serializer clt in
  let c = connect s srv in
  send c 1; send c 2; send c 3;
  let m1 = recv c in
  let m2 = recv c in
  let m3 = recv c in
  assert (m1 = 1 && m2 = 2 && m3 = 3)
*)
