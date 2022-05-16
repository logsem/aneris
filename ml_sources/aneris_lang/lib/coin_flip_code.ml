open! Ast

let coin_flip () =
  let l = ref true in
  fork (fun () -> l := false) ();
  !l
