open Unix
open Ast
open Serialization_code
open List_code
open Par_code
open Network_util_code
open Vr_client_proxy_code
open Vr_replica_code

let list_to_alist l = List.fold_left (fun acc x -> list_cons x acc) list_nil (List.rev l)

let ip = (gethostbyname "localhost").h_addr_list.(0)

let m00 = makeAddress (string_of_inet_addr ip) 1100
let m01 = makeAddress (string_of_inet_addr ip) 1101
let m02 = makeAddress (string_of_inet_addr ip) 1102
let m03 = makeAddress (string_of_inet_addr ip) 1103
let m04 = makeAddress (string_of_inet_addr ip) 1104

let m10 = makeAddress (string_of_inet_addr ip) 1110
let m11 = makeAddress (string_of_inet_addr ip) 1111
let m12 = makeAddress (string_of_inet_addr ip) 1112
let m13 = makeAddress (string_of_inet_addr ip) 1113
let m14 = makeAddress (string_of_inet_addr ip) 1114

let m20 = makeAddress (string_of_inet_addr ip) 1120
let m21 = makeAddress (string_of_inet_addr ip) 1121
let m22 = makeAddress (string_of_inet_addr ip) 1122
let m23 = makeAddress (string_of_inet_addr ip) 1123
let m24 = makeAddress (string_of_inet_addr ip) 1124

let m30 = makeAddress (string_of_inet_addr ip) 1130
let m31 = makeAddress (string_of_inet_addr ip) 1131
let m32 = makeAddress (string_of_inet_addr ip) 1132
let m33 = makeAddress (string_of_inet_addr ip) 1133
let m34 = makeAddress (string_of_inet_addr ip) 1134

let m40 = makeAddress (string_of_inet_addr ip) 1140
let m41 = makeAddress (string_of_inet_addr ip) 1141
let m42 = makeAddress (string_of_inet_addr ip) 1142
let m43 = makeAddress (string_of_inet_addr ip) 1143
let m44 = makeAddress (string_of_inet_addr ip) 1144

let c01 = makeAddress (string_of_inet_addr ip) 1191
let c02 = makeAddress (string_of_inet_addr ip) 1192

let vr0 = list_to_alist [ m00; m10; m20; m30; m40 ]
let vr1 = list_to_alist [ m01; m11; m21; m31; m41 ]
let vr2 = list_to_alist [ m02; m12; m22; m32; m42 ]
let vr3 = list_to_alist [ m03; m13; m23; m33; m43 ]
let vr4 = list_to_alist [ m04; m14; m24; m34; m44 ]

let prx = list_to_alist [ m00; m11; m22; m33; m44 ]
let cfg = list_to_alist [ vr0; vr1; vr2; vr3; vr4 ]

let vsr = int_serializer

let wait rd key =
  let rec loop () =
    match rd key with
    | None -> loop ()
    | Some x -> x
  in loop ()


let th1 wr () =
  ignore(wr "x" 13);
  ignore(wr "y" 21);
  ignore(wr "s1" 11)

let th2 wr () =
  ignore(wr "x" 34);
  ignore(wr "y" 55);
  ignore(wr "s2" 11)


let runner cfg =
  sendTo_sim_flag := true;
  set_send_fault_flags 10 0 750;
  monitor_send_faults ();
  Printf.printf "step 0: install proxies.\n%!";
  let (wr1, rd1) = install_proxy vsr prx c01 in
  let (wr2, rd2) = install_proxy vsr prx c02 in
  Printf.printf "step 1: install vr service.\n%!";
  fork (Printf.printf "><><>fork 0<><><\n%!"; init vsr cfg) 0;
  fork (Printf.printf "><><>fork 1<><><\n%!"; init vsr cfg) 1;
  fork (Printf.printf "><><>fork 2<><><\n%!"; init vsr cfg) 2;
  fork (Printf.printf "><><>fork 3<><><\n%!"; init vsr cfg) 3;
  fork (Printf.printf "><><>fork 4<><><\n%!"; init vsr cfg) 4;
  Printf.printf "step 2: run write requests.\n%!";
  ignore(par (th1 wr1) (th2 wr2));
  Printf.printf "step 3: run read requests.\n%!";
  let (x1, y1) =
    ignore(wait rd1 "s2");
    (unSOME (rd1 "x"), unSOME (rd1 "y")) in
   let (x2, y2) =
    ignore(wait rd2 "s1");
    (unSOME (rd2 "x"), unSOME (rd2 "y")) in
  Printf.printf "step 4: print results.\n%!";
  Printf.printf "\n><><><><><><><><><><><><><><><><><><><><><><>%!";
  Printf.printf "\n[client1] (x,y) : (%d,%d)%!" x1 y1;
  Printf.printf "\n><><><><><><><><><><><><><><><><><><><><><><>%!";
  Printf.printf "\n[client2] (x,y) : (%d,%d)%!" x2 y2;
  Printf.printf "\n><><><><><><><><><><><><><><><><><><><><><><>%!"

let () =  runner cfg
