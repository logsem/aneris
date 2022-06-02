open Ast
open List_code

type 'a log  = ('a alist * int) Atomic.t

(* -------------------------------------------------------------------------- *)
(** Operations on log of requests *)
(* -------------------------------------------------------------------------- *)

(* TODO: The logs below should use by resizeable arrays instead of lists! *)
let log_create () : 'a log = ref (list_nil, 0) (* the log and next free index. *)

let log_add_entry (log : 'a log) (req : 'a) =
  let lp = !log in
  let (data, next) = lp in
  let data' = list_append data (list_cons req list_nil) in
  log := (data', next + 1)

let log_next (log : 'a log) = snd !log

let log_length (log : 'a log) = snd !log

let log_get (log : 'a log) (i : int) : 'a option =
  list_nth (fst !log) i

let log_wait_until log mon i : unit =
  let rec aux () =
    let n = log_next log in
    if n = i then begin monitor_wait mon; aux () end
    else assert (i < n)
  in
  if i < 0 ||log_next log < i then assert false
  else aux ()

(* let log_get_suf (i: int) (log : 'a log) : 'a log_entry alist * int =
 *   (list_suf i (fst !log), (snd !log - i)) *)
