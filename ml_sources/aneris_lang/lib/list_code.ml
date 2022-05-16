open! Ast

type 'a alist = ('a * 'a alist) option

let list_nil : 'a alist = None

[@@@NOTATION {|Notation "[ ]" := (list_nil) (format "[ ]") : expr_scope.|}]


let list_cons (elem : 'a) (list : 'a alist) : 'a alist = Some (elem, list)

[@@@NOTATION
  {|Infix "::" := list_cons (at level 60, right associativity) : expr_scope.|}]

[@@@NOTATION
  {|Notation "[ x ]" := (list_cons x list_nil) (format "[ x ]") : expr_scope.|}]

[@@@NOTATION
  {|Notation "[ x ; y ; .. ; z ]" := (list_cons x (list_cons y .. (list_cons z list_nil) ..)) : expr_scope.|}]

let list_head l =
  match l with
    Some a -> Some (fst a)
  | None -> None

let list_tail l =
  match l with
    Some a -> (snd a)
  | None -> None

let rec list_fold handler acc l =
  match l with
    Some a -> let f = fst a in
      let s = snd a in
      let acc = (handler acc f) in
      list_fold handler acc s
  | None -> acc

let rec list_iter handler l =
  match l with
    Some a ->
     let tail = snd a in
     handler (fst a);
     list_iter handler tail
  | None -> ()

(* TODO: inline once we know how to prove the inlined version *)
let rec list_iteri_loop handler i l =
  match l with
    Some a ->
      let tail = snd a in
      handler i (fst a);
      list_iteri_loop handler (i + 1) tail
  | None -> ()

let list_iteri handler l =
  list_iteri_loop handler 0 l

(* TODO: this shouldn't be exposed as a function, since it's just
   a helper for list_mapi. However, it is exposed so we can prove a helper lemma
   by induction. Fix the proof and inline this function. *)
let rec list_mapi_loop f k l =
  match l with
    Some a -> list_cons (f k (fst a)) (list_mapi_loop f (k + 1) (snd a))
  | None -> None 

(* Non tail-recusive, like its OCaml counterpart:
   https://ocaml.org/api/List.html *)
let list_mapi f l =
  list_mapi_loop f 0 l

(* Non tail-recursive *)
let rec list_map f l =
  match l with
    Some a -> list_cons (f (fst a)) (list_map f (snd a))
  | None -> None

(* Non tail-recursive *)
let rec list_filter f l =
  match l with
    Some a ->
      let r = list_filter f (snd a) in
      if (f (fst a)) then list_cons (fst a) r
      else r
  | None -> None

let rec list_length l =
  match l with
    Some a -> 1 + list_length (snd a)
  | None -> 0

let rec list_nth l i =
  match l with
    Some a ->
      if i = 0 then Some (fst a)
      else list_nth (snd a) (i - 1)
  | None -> None

let rec list_mem x l =
  match l with
    Some a ->
      let head = fst a in
     let tail = snd a in
     (x = head) || list_mem x tail
  | None -> false

 let rec list_find_remove f l =
  match l with
    Some a ->
     let head = fst a in
     let tail = snd a in
     if f head then Some (head, tail)
     else
       let r = list_find_remove f tail in
       (match r with
          Some b ->
           let head' = fst b in
           let tail' = snd b in
           Some (head', list_cons head tail')
        | None -> None)
    | None -> None

let rec list_sub i l =
  if i <= 0 then list_nil
  else
    match l with
      Some a -> list_cons (fst a) (list_sub (i - 1) (snd a))
    | None -> list_nil

let rec list_rev_aux l acc =
  match l with
    None -> acc
  | Some p ->
      let h = fst p in
      let t = snd p in
      let acc' = list_cons h acc in
      list_rev_aux t acc'

let list_rev l = list_rev_aux l list_nil

let rec list_append l r =
  match l with
    None -> r
  | Some p ->
     let h = fst p in
     let t = snd p in
     list_cons h (list_append t r)


let list_is_empty l =
  match l with
    None -> true
  | Some _p -> false


let rec list_forall test l =
  match l with
    None -> true
  | Some p ->
     let h = fst p in
     let t = snd p in
     test h && list_forall test t

let rec list_make len init =
  if len = 0 then list_nil
  else list_cons init (list_make (len - 1) init)

let list_init len f =
  let rec aux acc i =
    if i = len then list_rev acc
    else aux (list_cons (f i) acc) (i + 1)
  in aux list_nil 0

let rec list_update l i v =
  match l with
    Some a ->
      if i = 0 then list_cons v (list_tail l)
      else list_cons (fst a) (list_update (snd a) (i - 1) v)
    | None -> list_nil

(* TODO: move to the lib *)
(* Pre: 0 ≤ i < len *)
(* Post: returns l[i .. |l|[ *)
let rec list_suf i (l : 'a alist) : 'a alist =
  if i = 0 then l
  else match l with
    | None   -> None
    | Some p -> list_suf (i - 1) (snd p)

(* TODO: move to the lib *)
(* Pre: 0 ≤ i < |l| ∧ 0 <= i + ofs <= |l| *)
(* Post: returns  l[i..i+ofs[ *)
let list_inf_ofs i ofs l =
  if ofs <= 0 then list_nil else list_sub ofs (list_suf i l)

(* Pre: 0 ≤ i <= j < |l| *)
(* Post: returns l[i..j] *)
let list_inf i j l = list_inf_ofs i (j - i + 1) l

(* returns l[0..i-1], l[i..|l|] *)
let rec list_split i l =
  if i <= 0 then (list_nil, l)
  else
    match l with
      None -> (list_nil, list_nil)
    | Some p ->
      let (x, tl) = p in
      let ps = list_split (i - 1) tl in
      (list_cons x (fst ps), snd ps)
