open Ast
open Queue_code
open Map_code
open Serialization_code
open Network_util_code
open Client_server_printing

let tag_int_ser = (prod_serializer string_serializer int_serializer)

let idmsg_ser (ser[@metavar]) =
  sum_serializer
    int_serializer
    (prod_serializer int_serializer ser)

let gen_msg_ser (ser[@metavar]) =
  sum_serializer tag_int_ser (idmsg_ser ser)


type 'a sid_message  = int * 'a
type init_message    = string * int
type 'a messageQueueOut = 'a queue
type 'a messageQueueIn = 'a queue

type 'a gen_message  = (init_message, (int, 'a sid_message) sumTy) sumTy

type 'a msg_ser_ser = 'a gen_message -> string
type 'b msg_ser_deser = string -> 'b gen_message
type ('a, 'b) skt = (Unix.file_descr * ('a msg_ser_ser * 'b msg_ser_deser))

type ('a, 'b) chan_descr =
  ((('a messageQueueOut Atomic.t * monitor) *
   ('b messageQueueIn Atomic.t * Mutex.t)))

type ('a, 'b) conn_state = (int, ((('a, 'b) chan_descr * int) * (int Atomic.t * int Atomic.t))) sumTy
type ('a, 'b) conn_map = (saddr, ('a, 'b) conn_state) amap
type ('a, 'b) conn_queue = (('a, 'b) chan_descr * saddr) queue

type ('a, 'b) client_skt = ('a, 'b) skt

type ('a, 'b) server_skt_passive_data =
  ((Unix.file_descr * ('a msg_ser_ser * 'b msg_ser_deser)) * ('a, 'b) conn_map Atomic.t) * (('a, 'b) conn_queue Atomic.t * Mutex.t)

type ('a, 'b) server_skt =
  ((Unix.file_descr * ('a msg_ser_ser * 'b msg_ser_deser)), (('a, 'b) conn_queue Atomic.t * Mutex.t)) sumTy Atomic.t


(** ********************** CLIENT AND SERVER SOCKETS *********************** **)

(** UDP socket bundled together with serialization.
    This should be useful to avoid propagation of serialization as
    a parameter to objects using sockets, since any object containing
    the socket would already have access to serialization.
    Note also that the creation and binding of the socket is merged into
    one step. **)

let make_skt (ser[@metavar]) (deser[@metavar]) (sa : saddr) : ('a, 'b) skt =
  let sh = udp_socket () in
  socketBind sh sa;
  ((sh, ((gen_msg_ser ser).s_ser, (gen_msg_ser deser).s_deser)))

(** Client socket is just a alias of skt, with purpose to make the API
    more clear w.r. to distinction with server_socket (passive socket). *)

let make_client_skt (ser[@metavar]) (deser[@metavar]) (sa : saddr) :
  ('a,'b) client_skt =
  make_skt ser deser sa

(** Server socket carries data  (client-addr table, established connection queue)
    that are usually in charge of kernel, but here are simulated on top of UDP *)

let make_server_skt (ser[@metavar]) (deser[@metavar]) (sa : saddr) : ('a, 'b) server_skt =
  let skt = make_skt ser deser sa in
  ref (InjL skt)

(** New channel_descriptor *)
let make_new_channel_descr () : ('a, 'b) chan_descr =
  let sbuf = ref (queue_empty ()) in
  let rbuf = ref (queue_empty ()) in
  let smon = new_monitor () in
  let rlk = newlock () in
  ((sbuf, smon), (rbuf, rlk))


(** *********************** AUXIALIARY FUNCTIONS *************************** **)

let send_from_chan_loop
    (skt : ('a, 'b) client_skt) (sa : saddr) sidLBloc (c : ('a, 'b) chan_descr) : unit =
  let sdata = fst c in
  let (sbuf, smon) = sdata in
  let ((sh, (ser, _deser))) = skt in
  let send_msg lb i m =
    let msg = ser (InjR (InjR (lb + i, m))) in
    ignore(sendTo sh msg sa);
    unsafe (__print_send_msg ser sa (InjR (InjR (lb+i, m))));
  in
  let rec while_empty_loop p =
    if queue_is_empty !p
    then (monitor_wait smon; while_empty_loop p)
    else () in
  let rec loop () =
    monitor_acquire smon;
    while_empty_loop sbuf;
    let send_msg' = send_msg (!sidLBloc) in
    queue_iteri send_msg' !sbuf;
    monitor_release smon;
    unsafe (fun () -> Unix.sleepf 0.35);
    loop ()
  in
  loop ()

let prune_sendbuf_at_ack
    (smon : monitor)
    (sidLBloc : int Atomic.t)
    (sendbuf : 'a messageQueueOut Atomic.t) msg_ack =
  let sidLB = !sidLBloc in
  (* Check whether ack has been seen already. *)
  if msg_ack <= sidLB then ()
  else      (* If the incoming ack number is more recent than local ackid, *)
    begin   (* then update the ackid and the outbuf. *)
      monitor_acquire smon;
      let qe = !sendbuf in
      sidLBloc := msg_ack;
      sendbuf := (queue_drop qe (msg_ack - sidLB));
      monitor_release smon
    end


let process_data_on_chan
    (skt : ('a, 'b) skt)
    (sa : saddr)
    (sidLB : int Atomic.t)
    (ackId : int Atomic.t)
    (c : ('a, 'b) chan_descr)
    (msg : (int, 'b sid_message) sumTy) : unit =
  let ((sbuf, smon), (rbuf, rlk)) = c in
  let ((sh, (ser, _deser))) = skt in
  let ackid = !ackId in
  begin match msg with
    | InjL id -> prune_sendbuf_at_ack smon sidLB sbuf id
    (* Message is from the other end *)
    | InjR cmsg ->
      let (mid, mbody) = cmsg in
      let () =
        (* If the message is just the next new message, *)
        if mid = ackid
        then    (* then update ackid and enqueue the message *)
          begin
            acquire rlk;
            rbuf := queue_add mbody !rbuf;
            ackId := mid + 1;
            release rlk;
          end
        else () (* Otherwise, the message is not new or is too fresh, drop it. *)
      in
      (* Not matter what, send an acknowledgement with the current ackId. *)
      (* The acknowledgment number in an ACK is the next expected sequence
         number for the end sending the ACK. *)
      let msg_ack = ser (InjR (InjL !ackId)) in
      ignore (sendTo sh msg_ack sa);
      unsafe (__print_send_msg ser sa (InjR (InjL !ackId)))
  end

let client_recv_on_chan_loop
    (skt : ('a, 'b) skt) (sa : saddr)
    (sidLB : int Atomic.t)
    (ackId : int Atomic.t)
    (c : ('a, 'b) chan_descr) : unit =
  let ((sh, (_ser, deser))) = skt in
  let rec loop () =
    let msg = unSOME (receiveFrom sh) in
    assert (sa = snd msg);
    unsafe (__print_recv_msg deser sa msg);
    begin match deser (fst msg) with
    | InjL _abs -> ()
    | InjR sm -> process_data_on_chan skt sa sidLB ackId c sm
    end;
    loop ()
  in loop ()


let resend_listen skt dst req handler =
  let rec aux () =
    match receiveFrom skt with
    | Some m ->
      let msg = fst m in
      let sender = snd m in
      handler msg sender
    | None ->
      ignore(sendTo skt req dst);
      unsafe (__print_send_handshake_msg dst req);
      aux ()
  in aux ()

let client_conn_step
    (skt : ('a, 'b) client_skt) (req : init_message) (repl_tag : string) (saddr : saddr) =
  let ((sh, (ser, deser))) = skt in
  let req_msg = ser (InjL req) in
  ignore (sendTo sh req_msg saddr);
  unsafe (__print_send_msg ser saddr (InjL req));
  let rec handler msg src =
    match deser msg with
    | InjL repl ->
      unsafe (__print_recv_msg deser saddr (msg, src));
      let (tag, data) = repl in
      if ((tag = repl_tag) && (src = saddr))
      then data
      else resend_listen sh saddr req_msg handler
    | InjR _sm ->
      (* TODO: show later that this is actually absurd case. *)
      resend_listen sh saddr req_msg handler
  in resend_listen sh saddr req_msg handler

let server_conn_step_to_open_new_conn (srv_skt : ('a, 'b) server_skt_passive_data) bdy clt_addr =
  let ((skt, connMap), (_chanQueue, _connlk)) = srv_skt in
  let ((sh, (ser, _deser))) = skt in
  match bdy with
  | InjL im ->
    if (fst im = "INIT" && snd im = 0)
    then begin
      let cookie = rand 1073741823 in
      connMap := map_insert clt_addr (InjL cookie) !connMap;
      let init_ack = ser (InjL ("INIT-ACK", cookie)) in
      ignore (sendTo sh init_ack clt_addr);
      unsafe (__print_send_msg ser clt_addr (InjL ("INIT-ACK", cookie)))
    end
    else assert false
  | InjR _abs -> assert false

let server_conn_step_to_establish_conn (srv_skt : ('a, 'b) server_skt_passive_data) cookie bdy clt_addr =
  let ((skt, connMap), (chanQueue, connlk)) = srv_skt in
  let ((sh, (ser, _deser))) = skt in
  match bdy with
  | InjL im ->
    if ((fst im = "COOKIE") && (snd im = cookie))
    then begin
      let sidLB = ref 0 in
      let ackId = ref 0 in
      let chan_descr = make_new_channel_descr () in
      fork (send_from_chan_loop skt clt_addr sidLB) chan_descr;
      connMap := map_insert clt_addr
          (InjR ((chan_descr, cookie), (sidLB, ackId))) !connMap;
      let cookie_ack = ser (InjL ("COOKIE-ACK", 0)) in
      ignore (sendTo sh cookie_ack clt_addr);
      unsafe (__print_send_msg ser clt_addr (InjL ("COOKIE-ACK", 0)));
      acquire connlk;
      chanQueue := queue_add (chan_descr, clt_addr) !chanQueue;
      release connlk;
      unsafe (__print_new_chan clt_addr)
    end
    else
    if (fst im = "INIT" && snd im = 0)
    then begin
      (* In principle, we could generate and store a new cookie? *)
      let init_ack = ser (InjL ("INIT-ACK", cookie)) in
      ignore (sendTo sh init_ack clt_addr);
      unsafe (__print_send_msg ser clt_addr (InjL ("INIT-ACK", cookie)));
    end
    else assert false
  | InjR _abs -> assert false

let server_conn_step_process_data ( srv_skt : ('a, 'b) server_skt_passive_data) chan_data bdy clt_addr =
  let skt = fst (fst srv_skt) in
  let ((sh, (ser, _deser))) = skt in
  let ((chan_descr, cookie), (sidLB, ackId)) = chan_data in (* Completed connection *)
  match bdy with
  | InjL im ->
    if ((fst im = "COOKIE") && (snd im = cookie))
    then
      begin
        let cookie_ack = ser (InjL ("COOKIE-ACK", 0)) in
        ignore (sendTo sh cookie_ack clt_addr);
        unsafe (__print_send_msg ser clt_addr (InjL ("COOKIE-ACK", 0)));
      end
    else ()
  | InjR sm -> process_data_on_chan skt clt_addr sidLB ackId chan_descr sm

(** ******** ESTABLISHING CONNECTION (server_listen, accept, connect) ****** **)

let server_recv_on_listening_skt_loop (srv_skt : ('a, 'b) server_skt_passive_data) : unit =
  let ((skt, connMap), _conn_data) = srv_skt in
  let ((sh, (_ser, deser))) = skt in
  let rec loop () =
    let msg = unSOME (receiveFrom sh) in
    let (m, clt_addr) = msg in
    unsafe (__print_recv_msg deser clt_addr msg);
    let bdy = deser m in
    begin (* Check whether the client has been registered. *)
      match map_lookup clt_addr !connMap with
      | None -> server_conn_step_to_open_new_conn srv_skt bdy clt_addr
      | Some data ->
        match data with
        | InjL cookie -> server_conn_step_to_establish_conn srv_skt cookie bdy clt_addr
        | InjR p -> server_conn_step_process_data srv_skt p bdy clt_addr
    end; loop ()
  in loop ()

let server_listen (srv_skt : ('a, 'b) server_skt) : unit =
  match !srv_skt with
  | InjL skt ->
    let connMap = ref (map_empty ()) in
    let connQueue = ref (queue_empty ()) in
    let connlk = newlock () in
    srv_skt := InjR (connQueue, connlk);
    let srv_skt_passive = ((skt, connMap), (connQueue, connlk)) in
    fork server_recv_on_listening_skt_loop srv_skt_passive;
  | InjR _queue -> assert false


let accept (srv_skt : ('a, 'b) server_skt) : ('a, 'b) chan_descr * saddr =
  match !srv_skt with
  | InjL _skt -> assert false
  | InjR queue ->
    let (chanQueue, connlk) = queue in
    let rec aux () =
      acquire connlk;
      if (queue_is_empty !chanQueue)
      then begin
        release connlk;
        unsafe (fun () -> Unix.sleepf 1.0);
        aux ()
      end
      else begin
        let q = unSOME (queue_take_opt !chanQueue) in
        let ((c, clt_addr), tl) = q in
        ignore(chanQueue := tl);
        release connlk;
        (c, clt_addr)
      end
    in aux ()

let connect (skt : ('a, 'b) client_skt) (srv_addr : saddr) : ('a, 'b) chan_descr =
  setReceiveTimeout (fst skt) 1 0;
  let cookie = client_conn_step skt ("INIT", 0) "INIT-ACK" srv_addr in
  let _ack = client_conn_step skt ("COOKIE", cookie) "COOKIE-ACK" srv_addr in
  setReceiveTimeout (fst skt) 0 0;
  let sidLB = ref 0 in
  let ackId = ref 0 in
  let c = make_new_channel_descr () in
  fork (send_from_chan_loop skt srv_addr sidLB) c;
  fork (client_recv_on_chan_loop skt srv_addr sidLB ackId) c;
  c

(** ******************* DATA TRANSFER (send, try_recv, recv) *************** **)

let send (c : ('a, 'b) chan_descr) (mbody : 'a) =
  let sdata = fst c in
  let (sbuf, smon) = sdata in
  monitor_acquire smon;
  let qe = !sbuf in
  sbuf := queue_add mbody qe;
  monitor_signal smon;
  monitor_release smon

let try_recv (c : ('a, 'b) chan_descr) : 'b option =
  let rdata = snd c in
  let (rbuf, rlk) = rdata in
  acquire rlk;
  let mo = queue_take_opt !rbuf in
  let res =
    begin match mo with
      | None -> None
      | Some p ->
        let (msg, tl) = p in
        rbuf := tl;
        Some msg
    end in
  release rlk;
  res

let recv (c : ('a, 'b) chan_descr) : 'b =
  let rec aux () =
    match try_recv c with
    | None -> unsafe (fun () -> Unix.sleepf 0.15); aux ()
    | Some res -> res
  in aux ()
