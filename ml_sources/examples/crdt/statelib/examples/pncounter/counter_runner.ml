open Unix
open Ast
open List_code
open Counter_code
open Statelib_code


let handle_io i rd upd =
  let s = read_line () in
  match String.split_on_char ' ' s with
  | [ "read" ] -> Printf.printf "CTR[%n] : %n\n" i (rd ())
  | [ "inc"; v_str ] ->
      let v = int_of_string v_str in
      let () = upd v in
      Printf.printf "CTR[%n] : %n\n" i (rd ())
  | [ "dec"; v_str ] ->
      let v = int_of_string v_str in
      let () = upd (-v) in
      Printf.printf "CTR[%n] : %n\n" i (rd ())
  | "close" :: _ -> exit 0
  | _ -> Printf.printf "invalid command \n"

let init_exec () =
  if Array.length Sys.argv < 4 then (
    prerr_endline "Usage: <index> <port1 port2 ... portN>";
    exit 2);
  let ip = string_of_inet_addr (gethostbyname "localhost").h_addr_list.(0) in
  let l =
    let sa i = SADDR (ip, (int_of_string Sys.argv.(i + 2))) in
    list_init (Array.length Sys.argv - 2) sa
  in
  let i = int_of_string Sys.argv.(1) in
  let p = counter_init l i in
  let read = fst p in
  let update = snd p in
  loop_forever (fun () -> handle_io i read update)

let () = Unix.handle_unix_error init_exec ()
