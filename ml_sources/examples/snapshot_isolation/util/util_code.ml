open !Ast
open Serialization_code
open Snapshot_isolation_code

let commitU cst : unit =
  let _b = commit cst in ()

let commitT cst : unit =
  assert (commit cst)

let wait_transaction (cst : 'a connection_state)
    (cond : 'a -> bool) (k : string) : unit =
  let rec aux () =
    start cst;
    match read cst k with
    | None ->
      commitT cst; aux ()
    | Some v ->
      if cond v
      then (commitT cst)
      else (commitT cst; aux ())
  in aux ()

let run (cst : 'a connection_state)
    (handler : 'a connection_state -> unit) : bool =
  start cst;
  handler cst;
  commit cst
  
let run_client caddr kvs_addr tbody =
  unsafe (fun () -> Printf.printf "Start client.\n%!");
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  unsafe (fun () -> Printf.printf "Client started.\n%!");
  let b = run cst tbody in
  unsafe (fun () -> Printf.printf "Transaction %s.\n%!"
             (if b then "committed" else "aborted"))
