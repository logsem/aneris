open !Ast
open Serialization_code
open Snapshot_isolation_code

let commitU cst : unit =
  let _b = commit cst in ()

let commitT cst : unit =
  assert (commit cst)

(** Assumes cst is in the active state.
    Returns cst in the active state. *)
let wait_on_key (cst : int connection_state)
    (cond : 'a -> bool) (k : string) : unit =
  let rec aux () =
  match read cst k with
  | None ->
    commitU cst; start cst; aux ()
  | Some v ->
    if cond v
    then (commitU cst; start cst)
    else (commitU cst; start cst; aux ())
  in aux ()

(** Assumes cst is in the active state and no writes happened.
    Returns cst in the active state with no writes. *)
let wait_on_keyT (cst : int connection_state)
    (cond : 'a -> bool) (k : string) : unit =
  let rec aux () =
  match read cst k with
  | None ->
    commitT cst; start cst; aux ()
  | Some v ->
    if cond v
    then (commitT cst; start cst)
    else (commitT cst; start cst; aux ())
  in aux ()


let run_client caddr kvs_addr tbody =
  unsafe (fun () -> Printf.printf "Start client.\n%!");
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  unsafe (fun () -> Printf.printf "Client started.\n%!");
  let b = run cst tbody in
  unsafe (fun () -> Printf.printf "Transaction %s.\n%!"
             (if b then "committed" else "aborted"))
