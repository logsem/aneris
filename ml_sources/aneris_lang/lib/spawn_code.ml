open! Ast

let spawn f =
  let c = ref None in
  fork (fun () -> c := Some (f ())) ();
  c

let rec join c =
  match !c with
  | None -> join c
  | Some x -> x
