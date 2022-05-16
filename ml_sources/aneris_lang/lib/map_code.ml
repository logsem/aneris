open! Ast
open List_code
open Set_code

type ('a, 'b) amap = ('a * 'b) alist

let map_empty () : ('a, 'b) amap = list_nil

let map_remove (key : 'a) : ('a, 'b) amap -> ('a, 'b) amap =
  let rec loop (m : ('a, 'b) amap) =
    match m with
      None -> None
    | Some p ->
       if fst (fst p) = key
       then snd p
       else list_cons (fst p) (loop (snd p)) in
  loop

let map_insert key value m : ('a, 'b) amap =
  list_cons (key, value) (map_remove key m)

let map_lookup (key : 'a) : ('a, 'b) amap -> 'b option =
  let rec loop m =
    match m with
      None -> None
    | Some p -> if fst (fst p) = key
                then Some (snd (fst p))
                else loop (snd p)
  in loop

let map_mem (k : 'a) (m : ('a, 'b) amap) : bool =
  match map_lookup k m with
    None -> false
  | Some _p -> true

let rec map_dom (m : ('a, 'b) amap) : 'a aset =
  match m with
    None -> set_empty ()
  | Some p -> set_add (fst (fst p)) (map_dom (snd p))

let rec map_iter (f : 'a -> 'b -> 'c) (m :  ('a, 'b) amap) : unit =
  match m with
    None -> ()
  | Some p ->
      let entry = fst p  in
      f (fst entry) (snd entry);
      map_iter f (snd p)

let rec map_forall (f : 'a -> 'b -> bool) (m : ('a, 'b) amap) : bool =
  match m with
      None -> true
    | Some p  ->
       let entry = fst p in
       let t = snd p  in
       f (fst entry) (snd entry) && map_forall f t
