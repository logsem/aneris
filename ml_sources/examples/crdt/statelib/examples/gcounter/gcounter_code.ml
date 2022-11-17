open !Ast
open List_code
open Vector_clock_code
open Statelib_code

(* TODO : move to List_code *)
let rec list_map2 (f : 'a -> 'b -> 'c) (l : 'a alist) (l' : 'b alist) : 'c alist =
  match l with
    Some a ->
    begin
      match l' with
      | Some b ->
        list_cons (f (fst a) (fst b)) (list_map2 f (snd a) (snd b))
      | None -> assert false
    end
  | None -> None

let gcpt_init_st n = fun () -> vect_make n 0

let gcpt_mutator : (int, int alist) mutatorFnTy =
  fun (repId : int) (st : int alist) (op : int) ->
  match list_nth st repId with
  | None -> st
  | Some p -> vect_update st repId (op + p)

let max_fn i j = if i < j then j else i

let gcpt_merge st st' :'a alist = list_map2 max_fn st st'

let gcpt_crdt n : (int, int alist) crdtTy =
  fun () -> (((fun () -> gcpt_init_st n ()), gcpt_mutator), gcpt_merge)

let gcpt_init addrs rid =
  let len = list_length addrs in
  let initRes =
    statelib_init vect_serialize vect_deserialize addrs rid (gcpt_crdt len) in
  let get_state = fst initRes in
  let update = snd initRes in
  (get_state, update)
