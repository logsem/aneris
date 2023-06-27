(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/snapshot_isolation/examples/anomalies/anomalie_1/anomalie_1_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.examples.snapshot_isolation Require Import snapshot_isolation_code.
From aneris.examples.snapshot_isolation.util Require Import util_code.

Definition tbody_init : val :=
  λ: "s", write "s" #"x" #1;;
           write "s" #"y" #1;;
           write "s" #"s0" #1.

Definition wait_s0 : val :=
  λ: "s", wait_on_key "s" (λ: "v", "v" = #1) #"s0".

Definition tbody_xy : val :=
  λ: "s",
  wait_s0 "s";;
  let: "n" := unSOME (read "s" #"x") in
  (if: #0 < "n"
   then
     write "s" #"y" #(-1);;
     write "s" #"s1" #1;;
     #() (* unsafe (fun () -> Printf.printf "Set y to -1 \n%!"); *);;
     #() (* unsafe (fun () -> Unix.sleepf 0.5); *)
   else  #()).

Definition tbody_yx : val :=
  λ: "s",
  wait_s0 "s";;
  let: "n" := unSOME (read "s" #"y") in
  (if: #0 < "n"
   then
     write "s" #"x" #(-1);;
     write "s" #"s2" #1;;
     #() (* unsafe (fun () -> Printf.printf "Set x to -1 \n%!"); *);;
     #() (* unsafe (fun () -> Unix.sleepf 0.5); *)
   else  #()).

Definition tbody_read : val :=
  λ: "s",
  #() (* unsafe (fun () ->
      Random.self_init ();
      let r = Random.int 5 in
      Printf.printf "%d\n%!" r;
      Unix.sleep r *);;
  wait_s0 "s";;
  let: "n1" := unSOME (read "s" #"x") in
  let: "n2" := unSOME (read "s" #"y") in
  let: "vs1" := read "s" #"s1" in
  let: "vs2" := read "s" #"s2" in
  let: "b" := #0 ≤ ("n1" + "n2") in
  let: "_check" := (if: ("vs1" = (SOME #1)) && ("vs2" = (SOME #1))
   then  assert: (~ "b")
   else  assert: "b") in
  #() (* unsafe (fun () -> Printf.printf "(x,y) = (%d, %d) \n%!" n1 n2) *).

Definition node_init : val :=
  λ: "caddr" "kvs_addr", run_client "caddr" "kvs_addr" tbody_init.

Definition node_xy : val :=
  λ: "caddr" "kvs_addr", run_client "caddr" "kvs_addr" tbody_xy.

Definition node_yx : val :=
  λ: "caddr" "kvs_addr", run_client "caddr" "kvs_addr" tbody_yx.

Definition node_read : val :=
  λ: "caddr" "kvs_addr", run_client "caddr" "kvs_addr" tbody_read.

Definition server : val :=
  λ: "srv",
  #() (* unsafe (fun () -> Printf.printf "Start server.\n%!"); *);;
  init_server int_serializer "srv";;
  #() (* unsafe (fun () -> Printf.printf "Server started.\n%!") *).