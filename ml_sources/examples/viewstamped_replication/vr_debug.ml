open Ast

let int_log_to_string l =
  let rec aux l = match l with
    | None -> []
    | Some (h, tl) ->
      let ((op, addr), seqid) = h in
      let i = string_of_int seqid in
      let p = string_of_int (port_of_address addr) in
      match op with
      | InjL (s, r) ->
        let r = string_of_int r in
        let elt = "{cl:" ^ p ^ ", id:" ^ i ^ ", wr:" ^ s ^ " " ^ r ^ "}" in
        elt :: aux tl
      | InjR s ->
        let p = string_of_int (port_of_address addr) in
        let elt = "{cl:" ^ p ^ ", id:" ^ i ^ ", rd" ^ s ^ "}" in
        elt :: aux tl
  in
  String.concat ", " (aux l)


let print_first_line () =
  Printf.eprintf "    Event    | View | View mod i | Normal Mode | Op-Num | Commit-Num | \n%!"

let print_step_state _i ev vi prot prim opN cmtN _log () =
  Printf.eprintf "-----------------------------------------------------------------\n%!";
  Printf.eprintf "%-12s | %-4d | %-10d | %-11b | %-6d | %-10d | \n%!"
    ev vi prim prot opN cmtN
    (* (int_log_to_string log) *)

let print_step_state_vc _i ev vi prot prim opN cmtN _log sv dv () =
  Printf.eprintf "-----------------------------------------------------------------\n%!";
  Printf.eprintf "%-12s | %-4d | %-10d | %-11b | %-6d | %-10d | %-7d | %-7d \n%!"
    ev vi prim prot opN cmtN sv dv
    (* (int_log_to_string log) *)
