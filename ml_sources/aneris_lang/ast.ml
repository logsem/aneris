open Unix

type ('a, 'b) sumTy = InjL of 'a | InjR of 'b

(* let tpool = Domainslib.Task.setup_pool ~num_additional_domains:12 *)
let[@builtinAtom "Fork"] fork f e =
  let _promise =
    (* "num_domains" was "num_additional_domains", works with "num_domains" using domaislib 0.5.0 *)
    let tpool = Domainslib.Task.setup_pool ~num_domains:2 () in 
    Domainslib.Task.async tpool (fun () -> f e) in
  ()

let (!) = Atomic.get
let (:=) = Atomic.set
let ref = Atomic.make

let[@builtinAtom "CAS"] cas = Atomic.compare_and_set

let [@builtinAtom "RefLbl"] ref_lbl _s e = ref e

let[@builtinAtom "NewLock"] newlock = fun () -> Mutex.create ()
let[@builtinAtom "TryAcquire"] try_acquire = fun l -> Mutex.try_lock l
let[@builtinAtom "Acquire"] acquire = Mutex.lock

let[@builtinAtom "Release"] release = fun l -> Mutex.unlock l

type monitor = Condition.t * Mutex.t
let[@builtinAtom "New_Monitor"] new_monitor () = (Condition.create (), Mutex.create ())
let[@builtinAtom "Monitor_try_acquire"] monitor_try_acquire m = Mutex.try_lock (snd m)
let[@builtinAtom "Monitor_acquire"] monitor_acquire m = Mutex.lock (snd m)
let[@builtinAtom "Monitor_release"] monitor_release m = Mutex.unlock (snd m)
let[@builtinAtom "Monitor_signal"] monitor_signal m = Condition.signal (fst m)
let[@builtinAtom "Monitor_broadcast"] monitor_broadcast m = Condition.broadcast (fst m)
let[@builtinAtom "Monitor_wait"]  monitor_wait m = Condition.wait (fst m) (snd m)

type 'a serializer =
  { s_ser : 'a -> string;
    s_deser : string -> 'a}

let unsafe f =
  let _r = f () in ()

let print s l () = Printf.eprintf s l

let[@builtinAtom "FindFrom"] findFrom e0 e1 e2 =
  String.index_from_opt e0 e1 e2

let[@builtinAtom "Substring"] substring e0 e1 e2 =
  try String.sub e0 e1 e2
  with Invalid_argument _ -> ""

(* (UnOp StringLength e) *)
let[@builtinUnOp "StringLength"] strlen = String.length

(* (UnOp StringOfInt e) *)
let[@builtinUnOp "StringOfInt"] stringOfInt = string_of_int

(* Translate to UnOp IntOfString e *)
let[@builtinUnOp "IntOfString"] intOfString = int_of_string_opt

(* Translate to UnOp StringOfInt e *)
let[@builtinAtom "i2s"] i2s = string_of_int

(* Translate to UnOp IntOfString e *)
let[@builtinAtom "s2i"] s2i = int_of_string_opt



type saddr = SADDR of (string * int)

let to_saddr s =
  match s with
    ADDR_UNIX _ -> assert false
  | ADDR_INET (ip, p) -> SADDR (string_of_inet_addr ip, p)

let of_saddr s =
  match s with
  | SADDR (ip, p) -> ADDR_INET (inet_addr_of_string ip, p)


let ip_of_sockaddr s =
  match s with
    ADDR_UNIX _ -> assert false
  | ADDR_INET (ip, _) -> ip

let port_of_sockaddr s =
  match s with
    ADDR_UNIX _ -> assert false
  | ADDR_INET (_, p) -> p

let[@builtin "ip_of_address"] ip_of_address s =
  match s with
  | SADDR (ip, _) -> ip

let[@builtin "port_of_address"] port_of_address s =
  match s with
  | SADDR (_, p) -> p

let[@builtinAtom "MakeAddress"] makeAddress (ip : string) (port : int) =
  SADDR (ip, port)

let[@builtinAtom "GetAddrInfo"] get_address_info (s : saddr) =
  match s with | SADDR (ip, p) -> (ip, p)

let[@builtinAtom "NewSocket"] udp_socket () = socket PF_INET SOCK_DGRAM 0

let[@builtinAtom "ReceiveFrom"] receiveFrom skt =
  let buffer = Bytes.create 65536 in
  try
    match recvfrom skt buffer 0 65536 [] with
    | len, (ADDR_INET (_, _) as sockaddr) ->
      let msg = Bytes.sub_string buffer 0 len in
      Some (msg, to_saddr sockaddr)
    | _ -> assert false
  with
    Unix_error (EAGAIN, _,_)
  | Unix_error (EWOULDBLOCK, _, _) -> None

(* translate only name *)
let[@builtinAtom "SocketBind"] socketBind socket addr = bind socket (of_saddr addr)

let[@builtinAtom "Rand"] rand lim = Random.int lim

exception OnlyPosTimeout

let makeDecimal n =
  let f = float_of_int n in
  if n < 0 then raise OnlyPosTimeout;
  let rec aux q =
    if q < 1. then q
    else aux (q /. 10.)
  in aux f

(* translate only name *)
let[@builtinAtom "SetReceiveTimeout"] setReceiveTimeout sh n m =
  let fn = float_of_int n in
  let fm = makeDecimal m in
  Unix.setsockopt_float sh SO_RCVTIMEO (fn +. fm)

(* internal sendto *)
let sendTo skt msg sa =
  sendto skt (Bytes.of_string msg) 0 (String.length msg) [] (of_saddr sa)

(* Default values for simulation of send faults. *)
let drop_flag = ref 20
let delay_flag = ref 10
let dupl_flag = ref 20

let drop_cpt = ref 0
let delay_cpt = ref 0
let dupl_cpt = ref 0

let set_send_fault_flags dr de du =
  drop_flag := dr;
  delay_flag := de;
  dupl_flag := du

let print_send_faults () =
  Printf.eprintf "SEND FAULT STATS: drops = %d | delays = %d | dups = %d\n%!"
    !drop_cpt !delay_cpt !dupl_cpt

let monitor_send_faults () =
  let loop () =
    while true do
      Unix.sleepf 2.0;
      print_send_faults ();
    done in
  ignore (Thread.create loop ())

let[@builtinAtom "SendToSim"] sendTo_sim skt msg sa =
  let drop () = Atomic.incr drop_cpt; String.length msg in
  let delay () =
    ignore
      (Thread.create
         (fun () ->
            ignore(Unix.sleepf 0.01);
            Atomic.incr delay_cpt; sendTo skt msg sa)
         ());
    String.length msg in
  let duplicate () =
    ignore(sendTo skt msg sa);
    Atomic.incr dupl_cpt;
    sendTo skt msg sa in
  let () = Random.self_init () in
  let r = Random.int 1000 in
  if r < !drop_flag
  then drop ()
  else
  if !drop_flag <= r && r < !drop_flag + !dupl_flag
  then duplicate ()
  else
  if !drop_flag + !dupl_flag <= r && r < !drop_flag + !dupl_flag + !delay_flag
  then delay ()
  else sendTo skt msg sa

(* By default, set sendTo to normal sendTo without simulation. *)
let sendTo_sim_flag = ref false

let[@builtinAtom "SendTo"] sendTo skt msg sa =
  if !sendTo_sim_flag then sendTo_sim skt msg sa else sendTo skt msg sa
