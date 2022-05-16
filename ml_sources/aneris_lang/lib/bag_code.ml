open! Ast

let newbag () =
  let l = ref None in
  let v = newlock () in
  (l, v)

let insert x e =
  let l = fst x in
  let lock = snd x in
  acquire lock;
  l := Some (e, !l);
  release lock

let remove x =
  let l = fst x in
  let lock = snd  x in
  acquire lock;
   let r = !l in
   let res =
     match r with
       None -> None
     | Some p -> l := snd p; Some (fst p) in
   release lock;
   res
