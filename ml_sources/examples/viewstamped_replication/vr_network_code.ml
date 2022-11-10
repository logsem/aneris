open Ast
open List_code
open Network_util_code
open Queue_code
open Serialization_code
open Vr_serialization_code

(** Implementation of Retransmission/Acknowledgment (R/A) and
    Network/Application (N/A) communication layers of VR protocols *)

type outDataTy =
  ((((Mutex.t
      * int Atomic.t)
     * int Atomic.t)
    * int Atomic.t)
   * (int * string) queue Atomic.t)

(* returns a cell cfg[i][j] *)
let cfg_cell (cfg : (saddr alist) alist) i j =
  let cfg_i  = unSOME (list_nth cfg i) in
  let addr_ij = unSOME (list_nth cfg_i j) in
  addr_ij

(* socket with non-blocking receive *)
let init_socket_ij cfg i j =
  let sh = udp_socket () in
  let addr = cfg_cell cfg i j in
  (if i = j
   then setReceiveTimeout sh 2 0
   else
   if j = 0 (* Initial primary. *)
   then setReceiveTimeout sh 15 0
   else setReceiveTimeout sh 3 0);
  socketBind sh addr;
  sh

(* returns a list of socket handlers *)
let init_sockets cfg i =
  let len = list_length cfg in
  let rec aux j =
    if len <= j then list_nil
    else
      let sh = init_socket_ij cfg i j in
      list_cons sh (aux (j + 1))
  in aux 0

(** ------------------------------------------------------------------------- *)
(** ------------------------------- RECEIVING ------------------------------- *)
(** ------------------------------------------------------------------------- *)

let msgId_serializer =
  sum_serializer (int_serializer) (prod_serializer int_serializer string_serializer)

(** Remove all entires of outQ_j for which the sequence
    number is smaller than or equal to the ack number.
*)
let update_outQueue_j_at_ack ack_j lk_j outQ_j ack =
  let rec aux queue =
    if queue_is_empty queue
    then queue
    else
      let q = unSOME (queue_take_opt queue) in
      let (msg, queue') = q in
      if (fst msg) <= ack then aux queue'
      else queue (* Termination point: events that have not been acked. *)
  in
  acquire lk_j;
  (* Check whether ack has been seen already. *)
  if ack <= !ack_j then ()
  else      (* If the incoming ack number is more recent than local ack_j, *)
    begin   (* then update the ack_j and the outQ_j. *)
      ack_j := ack;
      let queue = aux !outQ_j in
      outQ_j := queue;
    end;
  release lk_j

let receive_from_j_at_i
    (val_ser[@metavar]) lk sh (mon : bool Atomic.t)
    (inQ :'a msgInTy queue Atomic.t) (outData_j : outDataTy) : unit =
  let ((((lk_j, _seqid_j), seen_j), ack_j), outQ_j) = outData_j in
  let rec loop () =
    begin (* At each step of the loop, call non-blocking receive. *)
      match receiveFrom sh with
      | None -> acquire lk; mon := false; release lk
      | Some msg ->
        let (mbody, msrc) = msg in
        let msgid = (msgId_serializer).s_deser mbody in
        (* A received msg is either an acknowledgement or an event. *)
        match msgid with
        | InjL ack -> (* If the msg is an ACK ack, we can maybe clean the outQ_j. *)
          update_outQueue_j_at_ack ack_j lk_j outQ_j ack
        | InjR mid -> (* Otherwise, the msg is an event. *)
          let (msg_id, msg_body) = mid in
          acquire lk_j;
          (* No matter what the event is, send a (possibly negative) acknowledgement,
             indicating to j what is its most recent event that has been seen. *)
          let msg_ack = ((msgId_serializer).s_ser (InjL !seen_j)) in
          let _sendack = sendTo sh msg_ack msrc in
          (* Check if the event has been seen already. *)
          if msg_id <= !seen_j
          then release lk_j     (* Ignore seen events.  *)
          else                  (* Process new evenets. *)
            begin
              seen_j := msg_id; (* Set the seen number to the event's id. *)
              release lk_j;
              acquire lk;
              let (event : 'a msgTy) = (msg_serializer val_ser).s_deser msg_body in
              inQ := queue_add (InjL event) !inQ;
              mon := true;
              release lk;
            end
    end;
    loop ()
  in
  loop ()

(** Monitor the client to ensure that if no requests from clients are
    coming, the primary will ping out backups with commit message.  *)
let receive_from_clients_at_ii (val_ser[@metavar]) lk sh mon
    (inQ : 'a msgInTy queue Atomic.t) =
  let rec loop () =
    let () =
      match receiveFrom sh with
      | None -> acquire lk; mon := false; release lk
      | Some msg ->
        let (event : 'a requestTy) = (request_serializer val_ser).s_deser (fst msg) in
        acquire lk;
        mon := true;
        inQ := queue_add (InjR event) !inQ;
        release lk in
    loop ()
  in loop ()

let fork_receive_threads (val_ser[@metavar] : 'a serializer) i lk
    (shl : Unix.file_descr alist)
    (mnl : bool Atomic.t alist)
    (outData : outDataTy alist)
    (inQ : 'a msgInTy queue Atomic.t) =
  let len = list_length shl in
  let rec aux j =
    if j < len
    then
      let sh = unSOME (list_nth shl j) in
      let mn = unSOME (list_nth mnl j) in
      let () =
        if j = i
        then fork (receive_from_clients_at_ii val_ser lk sh mn) inQ
        else
          let outData_j = unSOME (list_nth outData j) in
          fork (receive_from_j_at_i val_ser lk sh mn inQ) outData_j
      in
      aux (j + 1)
    else ()
  in aux 0


(** ------------------------------------------------------------------------- *)
(** --------------------------------- SENDING ------------------------------- *)
(** ------------------------------------------------------------------------- *)

(** Put a new serialized event in the j-th R/A layer queue. *)
let outqueue_msg (outData : outDataTy alist) j msg =
  let data_j = unSOME (list_nth outData j) in
  let ((((lk_j, seqid_j), _seen_j), _ack_j), outQ_j) = data_j in
  acquire lk_j;
  let idj = !seqid_j + 1 in
  seqid_j := idj;                         (* Assign a fresh sequence numer to the event. *)
  outQ_j := queue_add (idj, msg) !outQ_j; (* Add event in the queue. *)
  release lk_j

(** Dispatch a new serialized event to the R/A layer queues. *)
let outqueue_event_to_group (val_ser[@metavar]) len i
    (outData : outDataTy alist) (event : 'a msgTy) =
  let msg = (msg_serializer val_ser).s_ser event in
  let rec aux j =
    if j < len
    then
      if i = j then aux (j + 1) (* ignore q_ii, as clients are treated differently. *)
      else let () = outqueue_msg outData j msg in aux (j + 1)
    else ()
  in aux 0

let outqueue_msg_to_view_primary (val_ser[@metavar]) len
    (outData : outDataTy alist) (event : 'a msgTy) v =
  let j = v mod len in
  let msg = (msg_serializer val_ser).s_ser event in
  outqueue_msg outData j msg

(** Keep those functions for possible debugging purposes. *)
let send_prp (val_ser[@metavar]) len i outData prp_ev  =
  outqueue_event_to_group val_ser len i outData prp_ev

let send_cmt (val_ser[@metavar]) len i outData cmt_ev =
  outqueue_event_to_group val_ser len i outData cmt_ev

let send_pok (val_ser[@metavar]) len outData pok_ev  =
  let ((v, n), i) = pok_ev in
  outqueue_msg_to_view_primary val_ser len outData (pok v n i) v

let send_svc (val_ser[@metavar]) len i outData svc =
  outqueue_event_to_group val_ser len i outData svc

let send_dvc (val_ser[@metavar]) len outData dvc_ev =
  let (((((v, l), v'), n), k), i) = dvc_ev in
  outqueue_msg_to_view_primary val_ser len outData (dvc v l v' n k i) v

let send_snv (val_ser[@metavar]) len i outData snv_ev =
  outqueue_event_to_group val_ser len i outData snv_ev

let send_gst (val_ser[@metavar]) len outData gst_ev =
  let ((v, n), i) = gst_ev in
  outqueue_msg_to_view_primary val_ser len outData (gst v n i) v

let send_nst (val_ser[@metavar]) outData (nst_ev : 'a nstTy) =
  let ((((v, l), n), k), j) = nst_ev in
  let msg = (msg_serializer val_ser).s_ser (nst v l n k j) in
  outqueue_msg outData j msg

let send_rpl (val_ser[@metavar] : 'a serializer) i shl (reply_ev : 'a replyTy)  =
  let (_bdy, caddr) = reply_ev in
  let msg = (reply_serializer val_ser).s_ser reply_ev in
  let sh_ii = unSOME (list_nth shl i) in
  ignore(sendTo sh_ii msg caddr)

(** Process events emitted by the viewstamped replication. *)
let event_out_loop (val_ser[@metavar] : 'a serializer) len i lk shl outData outQ =
  let rec loop () =
    (* At each step of the loop, process an event from the outQ, if any. *)
    if queue_is_empty !outQ
    then unsafe (fun () -> Unix.sleepf 0.5)
    else begin
      acquire lk;
      let tmp = !outQ in
      if not (queue_is_empty tmp)
      then begin
        let q = unSOME (queue_take_opt tmp) in
        let (event, outq) = q in
        outQ := outq;
        release lk;
        begin
          match event with
          | InjL l___ -> begin
              match l___ with
              | InjL ll__->  begin
                  match ll__ with
                  | InjL lll_->  begin
                      match lll_ with
                      | InjL _llll -> send_prp val_ser len i outData l___
                      | InjR _lllr -> send_cmt val_ser len i outData l___
                    end
                  | InjR llr_ -> begin
                      match llr_ with
                      | InjL llrl  -> send_pok val_ser len outData llrl;
                      | InjR _llrr -> send_svc val_ser len i outData l___
                    end end
              | InjR lr__ -> begin
                  match lr__ with
                  | InjL lrl_ -> begin
                      match lrl_ with
                      | InjL lrll  -> send_dvc val_ser len outData lrll
                      | InjR _lrlr -> send_snv val_ser len i outData l___
                    end
                  | InjR rr_->  begin
                      match rr_ with
                      | InjL lrrl -> send_gst val_ser len outData lrrl
                      | InjR lrrr -> send_nst val_ser outData lrrr
                    end end end
          | InjR r___ -> send_rpl val_ser i shl r___
        end end
      else
        begin release lk; ()
        end
    end;
    (* And then loop. *)
    loop ()
  in loop ()


(** Sends serialized event messages in the outQ_j from node i to node j. *)
let send_from_i_to_j lk_j sh_ij addr_ji (outQ_j : (int * string) queue Atomic.t) =
  let rec sendAll q =
    if queue_is_empty q
    then ()
    else begin
      let q' = unSOME (queue_take_opt q) in
      let ((id, msg), tl) = q' in
      let msg = (msgId_serializer).s_ser (InjR (id,msg)) in
      ignore(sendTo sh_ij msg addr_ji);
      sendAll tl
    end in
  let rec loop () =
    acquire lk_j;
    let queue = !outQ_j in
    sendAll queue;
    release lk_j;
    loop ()
  in loop ()

(** Spawns |len|-1 sending threads for internal VR communication. *)
let fork_send_within_group_threads cfg i shl (outData : outDataTy alist) =
  let len = list_length cfg in
  let rec aux j =
    if j < len
    then
      if i = j then (* For simplicity, sending to cliens is handled differenty. *)
        aux (j + 1)
      else
        begin
          let sh_ij = unSOME (list_nth shl j) in
          let addr_ji = cfg_cell cfg j i in
          let data_j = unSOME (list_nth outData j) in
          (* Here, only lk_j and outQ_j matter. *)
          let ((((lk_j, _seqid_j), _seen_j), _ack_j), outQ_j) = data_j in
          fork (send_from_i_to_j lk_j sh_ij addr_ji) outQ_j;
          aux (j + 1)
        end
    else ()
  in aux 0

(** Initialize Retransmission/Acknowledgment (R/A)
    and Network/Application (N/A) communication layers *)
let init_network (val_ser[@metavar]) cfg i =
  let cfg_i = unSOME (list_nth cfg i) in
  let len = list_length cfg_i in
  (* Create socket handlers [s_(i,0), ... s_(i,i), ..., s_(i,|cfg|)].
     All socket handlers are in non-blocking mode with timeouts. *)
  let shl = init_sockets cfg i in
  (* Using those timeouts, use monitors to check
     if messages keep coming from other replicas. *)
  let monitors = list_init len (fun _j -> ref true) in
  (* Create lock for manipulating in-queue and out-queue, shared between
     the network and the application layers. *)
  let lk = newlock () in
  let (inQ : 'a msgInTy queue Atomic.t) = ref (queue_empty ()) in
  let (outQ : 'a msgOutTy queue Atomic.t) = ref (queue_empty ()) in
  (* Retransmission/acknowledgment (R/A) layer for communication with replica j. *)
  let create_data_j _j : outDataTy =
    let lock_j = newlock () in            (* A lock to update R/A layer data. *)
    let seqid_j = ref 0 in   (* Sequence number to order all events sent to j *)
    let seen_j = ref 0 in    (* The greatest sequence number of events received from j.   *)
    let ack_j = ref 0 in     (* The greatest sequence number of events acknowledged by j. *)
    let outQ_j = ref (queue_empty ()) in  (* The out-queue of indexed serialized events.  *)
    ((((lock_j, seqid_j), seen_j), ack_j), outQ_j) in
  let outData = list_init len create_data_j in
  (* Spawn |cfg|-1 sending threads. *)
  fork_send_within_group_threads cfg i shl outData;
  (* Spawn |cfg| receiving threads. *)
  fork_receive_threads val_ser i lk shl monitors outData inQ;
  (* Spawn loop for transmitting events out. *)
  fork (event_out_loop val_ser len i lk shl outData) outQ;
  (* Return application layer network data *)
  ((((lk, inQ), outQ), monitors), shl)
