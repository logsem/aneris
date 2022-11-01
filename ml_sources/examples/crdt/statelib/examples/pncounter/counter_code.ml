open !Ast
open Serialization_code
open Network_util_code
open List_code
open Statelib_code

type stTy = (int alist * int alist)

let mutate_side updl keepl i op : stTy =
  let v = unSOME (list_nth updl i) in
  (list_update updl i (v + op), keepl)

let mutator : (int, stTy) mutatorFnTy =
  fun (i : int) (cpt : stTy) (op : int) ->
  let (posl, negl) = cpt in
  if 0 <= op then mutate_side posl negl i op
  else mutate_side negl posl i (-op)

let merge_aux (l1 : int alist) (l2 : int alist) : int alist =
  let rec aux l r =
    match l with
    | None ->
      begin
        match r with
        | None -> None
        | Some _p -> assert false
      end
    | Some sl ->
      match r with
      | None -> assert false
      | Some sr ->
        let (x, slt) = sl in
        let (y, srt) = sr in
        let rs = if x <= y then y else x in
        let tl = aux slt srt in
        list_cons rs tl
  in aux l1 l2

let merge (st1 : stTy) (st2 : stTy) : stTy =
  let (pl1, nl1) = st1 in
  let (pl2, nl2) = st2 in
  let pres = merge_aux pl1 pl2 in
  let nres = merge_aux nl1 nl2 in
  (pres, nres)

let eval_state_aux (st : int alist) =
  list_fold (fun acc x -> acc + x) 0 st

let eval_state (st : stTy) : int =
  let (pl, nl) = st in
  let eval_pos = eval_state_aux pl in
  let eval_neg = eval_state_aux nl in
  eval_pos - eval_neg

let init_st () : stTy = (list_nil, list_nil)

let counter_crdt : (int, stTy) crdtTy =
  fun () -> ((init_st, mutator), merge)

let st_ser : stTy serializer = prod_serializer
    (list_serializer int_serializer)
    (list_serializer int_serializer)

let counter_init (addrs : saddr alist) (rid : int) =
  let initRes =
    statelib_init st_ser.s_ser st_ser.s_deser addrs rid counter_crdt in
  let (get_state, update) = initRes in
  let eval () = eval_state (get_state ()) in
  (eval, update)
