open Ast
open !Serialization_code
open !Network_util_code


let __print_recv_msg deser sa msg () =
  let (SADDR (s, i)) = sa in
  match deser (fst msg) with
  | InjL repl ->
    Printf.printf "(%s, %d) ---received---> HNDSHK packet %s,%d: \n%!"
      s i (fst repl) (snd repl)
  | InjR (InjL _) ->
    Printf.printf
      "(%s, %d) ---received---> ACKID packet: %s.\n%!" s i (fst msg)
  | InjR (InjR _) ->
    Printf.printf
      "(%s, %d) ---received---> SEQID packet: %s.\n%!" s i (fst msg)

let __print_send_msg ser sa bdy () =
  let msg = ser bdy in
  let (SADDR (s, i)) = sa in
  match bdy with
  | InjL init ->
     Printf.printf "(%s, %d) <-----send----- HNDSHK packet %s,%d: \n%!"
       s i (fst init) (snd init)
  | InjR (InjL _) ->
    Printf.printf
      "(%s, %d) <-----send----- ACKID packet: %s.\n%!" s i msg
  | InjR (InjR _) ->
    Printf.printf
      "(%s, %d) <-----send----- SEQID packet: %s.\n%!" s i msg

let __print_send_handshake_msg sa msg () =
  let (SADDR (s, i)) = sa in
     Printf.printf "(%s, %d) <-----send----- HNDSHK packet %s: \n%!"
       s i msg

let __print_new_chan clt_addr () =
  let (SADDR (s, i)) = clt_addr in
  Printf.printf "New channel created associated with saddr (%s, %d)\n%!" s i
