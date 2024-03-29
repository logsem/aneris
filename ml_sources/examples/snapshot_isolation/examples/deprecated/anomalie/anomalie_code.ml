(* open !Ast
open Serialization_code
open Network_util_code
open Par_code
open Snapshot_isolation_code
open Util_code


(** From the paper https://www.cs.umb.edu/~poneil/ROAnom.pdf
    A Read-Only Transaction Anomaly Under Snapshot Isolation
    By Alan Fekete, Elizabeth O'Neil, and Patrick O'Neil


    Possible outcomes for checking the balance :

  .-----------------------------------------------------------------------------------.
  | Case  | commit-order |  read values of (x,y) | balance (y-x) | Consistency Model  |
  |-------|--------------|-----------------------|---------------|--------------------|
  |  C0   | [        ]   |       (0, 0)          |      0        |                    |
  |  C1   | [T1      ]   |       (0, 20)         |     20        |                    |
  |  C2   | [      T2]   |     (-11, 0)          |    -11        |  SERIALIZABILITY   |
  |  C3   | [T1 ;  T2]   |     (-10, 20)         |     10        |                    |
  |  C4   | [T2 ;  T1]   |     (-11, 20)         |      9        |                    |
  |-------|--------------|-----------------------|---------------|--------------------|
  |  C5   | [T1 ;  T2]   |     (-11, 20)         |      9        | SNAPSHOT ISOLATION |
  |-----------------------------------------------------------------------------------|

  .-----------------------------------------------------------------------------.
  |            Possible (unordered) pairs of read-only transactions             |
  |------------------------------------------------------|----------------------|
  |  ( Ci, Ci )              for i in [0,4]              |                      |
  |  ( C0, Ci )              for i in [1,4]              |                      |
  |  ( C1, C3 )                                          |     SERIALIZABLE     |
  |  ( C2, C4 )                                          |                      |
  |------------------------------------------------------|----------------------|
  |  ( C0, C5 )                                          |   NOT SERIALIZABLE   |
  |  ( C1, C5 )                                          |                      |
  |  ( C3, C5 )                                          |                      |
  |  ( C5, C5 )                                          |                      |
  |------------------------------------------------------|----------------------|
  |  ( C1, C2 )                                          |     NOT POSSIBLE     |
  |  ( C1, C4 )                                          |                      |
  |  ( C2, C3 )                                          |                      |
  |  ( C2, C5 )                                          |                      |
  |  ( C3, C4 )                                          |                      |
  |  ( C4, C5 )                                          |                      |
  |------------------------------------------------------|----------------------|

  T1: ----------------[ W(Y,20) ]---------------------------------------------------
  T2: [ R(X,0) R(Y,0)                                W(X,-11) ]---------------------
  T3: ----------------------------[ R(X,0) R(Y,20) ]--------------------------------
  T4: ----------------------------------------------------------[ R(X,-11) R(Y,20) ]


*)


let tbody_init (s : int connection_state) : unit =
  write s "x" 0; write s "y" 0; write s "s0" 1

let wait_s0 (s : int connection_state) =
  wait_on_key s (fun v -> v = 1) "s0"

let tbody_withdraw_ten (s : int connection_state) : unit =
 unsafe (fun () ->
      Random.self_init ();
      let r = Random.int 5 in
      Printf.printf "%d\n%!" r;
      Unix.sleep r);
  wait_s0 s;
  let nx = unSOME (read s "x") in
  let ny = unSOME (read s "y") in
  let wdraw = nx + ny - 10 in
  if wdraw < 0 then begin
    write s "x" (nx - 10 - 1);
    unsafe (fun () ->
        Printf.printf "Withdrawed from checking account with penalty! \n%!");
  end
  else begin
    write s "x" (nx - 10);
    unsafe (fun () ->
        Printf.printf "Withdrawed from checking account without penalty. \n%!");
  end

let tbody_deposit_twenty (s : int connection_state) : unit =
  unsafe (fun () ->
      Random.self_init ();
      let r = Random.int 5 in
      Printf.printf "%d\n%!" r;
      Unix.sleep r);
  wait_s0 s;
  write s "y" 20;
  unsafe (fun () -> Printf.printf "Deposited twenty on saving account. \n%!")



let tbody_check_account_1 (r : (int * int) Atomic.t) (s : int connection_state) : unit =
  wait_s0 s;
  let n1 = unSOME (read s "x") in
  let n2 = unSOME (read s "y") in
  r := (n1, n2)

let tbody_check_account_2 (r : (int * int) Atomic.t) (s : int connection_state) : unit =
  wait_s0 s;
  let n1 = unSOME (read s "x") in
  let n2 = unSOME (read s "y") in
  r := (n1, n2)


let node_init caddr kvs_addr =
  run_client caddr kvs_addr tbody_init

let node_withdraw_ten caddr kvs_addr =
  run_client caddr kvs_addr tbody_withdraw_ten

let node_deposit_twenty caddr kvs_addr =
  run_client caddr kvs_addr tbody_deposit_twenty

let node_check_account caddr1 caddr2 kvs_addr =
  let r1 = ref (0,0) in
  let r2 = ref (0,0) in
  let _tt =
   par
     (fun () ->
         unsafe (fun () -> Unix.sleepf 1.5);
         run_client caddr1 kvs_addr (tbody_check_account_1 r1))
     (fun () ->
        unsafe (fun () -> Unix.sleepf 3.0);
        run_client caddr2 kvs_addr (tbody_check_account_2 r2))
  in
  let p1 = !r1 in
  let p2 = !r2 in
  let (x1, y1) = p1 in
  let (x2, y2) = p2 in
  unsafe (fun () -> Printf.printf "(x1,y1) = (%d, %d) \n%!" x1 y1);
  unsafe (fun () -> Printf.printf "(x2,y2) = (%d, %d) \n%!" x2 y2)


let server srv =
  unsafe (fun () -> Printf.printf "Start server.\n%!");
  init_server int_serializer srv;
  unsafe (fun () -> Printf.printf "Server started.\n%!") *)
