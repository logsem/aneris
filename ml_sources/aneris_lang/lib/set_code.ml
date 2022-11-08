open! Ast
open List_code

type 'a aset = 'a alist

let set_empty () : 'a aset = list_nil

let set_add : 'a -> 'a aset -> 'a aset =
  fun x s ->
  if list_mem x s then s
  else list_cons x s

[@@@NOTATION {|Notation "{[ x ]}" := (set_add x (set_empty #())) (at level 1, format "{[ x ]}") : expr_scope.|}]

[@@@NOTATION {|Notation "{[ x ; y ; .. ; z ]}" :=
  (set_add x (set_add y .. (set_add z (set_empty #())) ..)) : expr_scope.|}]

let set_mem : 'a -> 'a aset -> bool = list_mem

let set_iter : ('a -> unit) -> 'a aset -> unit = list_iter

let set_foldl : ('a -> 'b -> 'a) -> 'a -> 'b aset -> 'a = list_fold

let set_forall : ('a -> bool) -> 'a aset -> bool  = list_forall

let set_cardinal : 'a aset -> int = list_length

let set_subseteq : 'a aset -> 'a aset -> bool =
  fun x y ->  list_forall (fun e ->  set_mem e y) x

let set_equal : 'a aset -> 'a aset -> bool =
  fun x y ->  set_subseteq x y && set_subseteq y x

let set_union (s1 : 'a aset) (s2 : 'a aset) : 'a aset =
  set_foldl (fun su e -> set_add e su) s1 s2
