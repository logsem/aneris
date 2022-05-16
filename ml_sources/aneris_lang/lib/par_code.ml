(* #rectypes;; *)

open! Ast
open Spawn_code


let par e1 e2 =
  let handle = spawn e1 in
  let v2 = e2 () in
  let v1 = join handle in
  (v1, v2)

[@@@NOTATION {|Notation "e1 ||| e2" := (par (λ: <>, e1)%E (λ: <>, e2)%E) : expr_scope.|}]
[@@@NOTATION {|Notation "e1 ||| e2" := (par (λ: <>, e1)%V (λ: <>, e2)%V) : val_scope.|}]

(* NB: use unix command to trigger non-determinism, e.g.

let () =
  Printf.printf "---\n";
  let (l,x,r) = (ref 0, ref false, ref 0) in
  for _i = 1 to 100 do
    let _ = par
        (fun () -> Unix.sleepf 0.0000000001; x := true;
          (* Printf.printf "%d %!" 0 *)
        )
        (fun () -> Unix.sleepf 0.0000001;  x := false;
          (* Printf.printf "%d %!" 1 *)
        ) in
    (* Printf.printf "---\n%!"; *)
    if !x then incr l
    else incr r
  done;
  Printf.printf "res : (%d, %d)%!" !l !r in ()
*)
