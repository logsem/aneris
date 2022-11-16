open Ast
open List_code
open Queue_code
open Network_util_code
open Vector_clock_code
open Serialization_code

type 'a outqueues = (('a * vector_clock) * int) queue alist
type 'a inqueue = (('a * vector_clock) * int) alist

let rep_id_ser = int_ser

let rep_id_deser = int_deser

let seqnum_ser = int_ser

let seqnum_deser = int_deser

(* An ack has the format ((orig_id, seqnum), sender_id)
   `orig_id` is the replica id of the node that originally created the operation.
   `sender_id` is the replicae id of the node that sent the message with the ack.
   The two can be different because of re-transmissions.
*)
let ack_msg_ser = prod_ser (prod_ser rep_id_ser seqnum_ser)
                            rep_id_ser

let ack_msg_deser = prod_deser (prod_deser rep_id_deser seqnum_deser)
                                rep_id_deser

(* A broadcast message has the format (((payload, vc), orig_id), sender_id).
   See the comment above about the distinction between `orig_id` and `sender_id`.
*)
let broadcast_msg_ser (val_ser[@metavar]) =
  prod_ser (prod_ser (prod_ser val_ser vect_serialize)
                      rep_id_ser)
            rep_id_ser
let broadcast_msg_deser (val_deser[@metavar]) =
    prod_deser (prod_deser (prod_deser val_deser vect_deserialize)
                            rep_id_deser)
                rep_id_deser

let msg_ser (val_ser[@metavar]) =
  sum_ser ack_msg_ser (broadcast_msg_ser val_ser)

let msg_deser (val_deser[@metavar]) =
  sum_deser ack_msg_deser (broadcast_msg_deser val_deser)

let rec loop_forever thunk =
  thunk ();
  loop_forever thunk

let send_thread (val_ser[@metavar]) i socket_handler lock nodes outQueues =
  (* Send the first message in out-queue `q` to its destination *)
  let send_head j q =
    (* We don't send to ourselves, so the out-queue must be empty *)
    (* if (j = i) then (); assert (queue_is_empty q) TODO: prove this *)
    match (queue_peek_opt q) with
      Some msg ->
        (* This could be the first time we're sending this message, or we could be
          retransmitting it because it hasn't been acked.
          Don't remove the message from the queue, since we might
          need to retransmit in the future.  *)
          let dest = unSOME (list_nth nodes j) in
          (* Append to the message our id, since we're the sender *)
          ignore(sendTo socket_handler (msg_ser val_ser (InjR (msg, i))) dest)
      | None -> ()
  in
  loop_forever (fun () ->
    acquire lock;
    list_iteri send_head !outQueues;
    release lock;
    (* Thread.delay 1.0 *)
    )

let send_ack (val_ser[@metavar]) socket_handler origId sn senderId dest_addr =
  let ack = InjL ((origId, sn), senderId) in
  (* Since we're serializing an InjL, we can pass in a dummy 'val_ser'
     of 'unit_ser' *)
  let ack_raw = msg_ser val_ser ack in
  ignore(sendTo socket_handler ack_raw dest_addr)

let prune_ack origId sn q =
  match (queue_peek_opt q) with
    Some e ->
      let ((_p, vc), origMsg) = e in
      let snMsg = vect_nth vc origId in
      if (origMsg = origId && snMsg = sn) then
        let x = unSOME (queue_take_opt q) in
        let (_e, rest) = x in
        rest
      else
        q
  | None -> q

let recv_thread (val_ser[@metavar]) (val_deser[@metavar]) i socket_handler lock addrlst (inQueue : 'b inqueue Atomic.t) (outQueues : 'a outqueues Atomic.t) seen =
  let receive msg =
    match msg with
    | InjL ackMsg ->
      let ((origId, sn), senderId) = ackMsg in
      let senderQ = unSOME (list_nth !outQueues senderId) in
      let senderQ' = prune_ack origId sn senderQ in
      outQueues := list_update !outQueues senderId senderQ'
    | InjR bcstMsg ->
      let (((payload, vc), origId), senderId) = bcstMsg in
      let origSn = vect_nth vc origId in
      let senderAddr = unSOME (list_nth addrlst senderId) in
      (* acknowledge immediately *)
      send_ack val_ser socket_handler origId origSn i senderAddr;
      (* To determine whether to put this message in the in-queue,
         check that its seqnum is higher than the highest seqnum
         of the originator ever placed in the in-queue. *)
      let seenSn = vect_nth !seen origId in
      if (seenSn < origSn) then
      begin
        seen := vect_update !seen origId origSn;
        (* In stop-and-wait, origSn can be higher by at most one, because
           otherwise whoever sent origSn would've sent origSn - 1 first.
           *)
        (* assert (origSn = seenSn + 1); TODO: uncomment but mark as `unsafe` in the translation *)
        inQueue := list_cons ((payload, vc), origId) !inQueue;
        (* Now re-transmit the broadcast to all nodes other than the sender
           and the originator (and ourselves). *)
        outQueues := list_mapi (fun j q ->
            if (j <> i && j <> senderId && j <> origId) then
              (* Replace the sender id by our id, since we're the ones
                 sending the message this time. *)
              queue_add ((payload, vc), origId) q
            else q) !outQueues
      end
  in
  loop_forever (fun () ->
    let msg_raw = fst (unSOME (receiveFrom socket_handler)) in
    let msg = msg_deser val_deser msg_raw in
    acquire lock;
    receive msg;
    release lock)

let is_causally_next vc my_rid =
  let l = list_length vc in
  fun ev ->
    let ((_payload, ev_vc), orig) = ev in
    if my_rid = orig then
      false
    else if orig < l then
      vect_applicable ev_vc vc orig
    else
      false

let deliver vc lock inQueue rid () =
  acquire lock;
  let remRes = list_find_remove (is_causally_next !vc rid) !inQueue in
  let res =
    match remRes with
    | Some p ->
      let (elem, rest) = p in
      let ((payload, msgVc), orig) = elem in
      inQueue := rest;
      vc := vect_inc !vc orig;
      Some ((payload, msgVc), orig)
    | None -> None
  in
  release lock;
  res

let broadcast vc seen (outQueues : 'a outqueues Atomic.t) lock rid payload =
  acquire lock;
  vc := vect_inc !vc rid;
  let msg = ((payload, !vc), rid) in
  let sn = vect_nth !vc rid in
  (* let seenSn = vect_nth !seen rid in *)
  (* assert (sn = seenSn + 1); TODO: uncomment and mark this as unsupported *)
  seen := vect_update !seen rid sn;
  outQueues := list_mapi (fun j q ->
    (* rid added twice since orig = sender *)
    if (j <> rid) then queue_add msg q
    else q) !outQueues;
  release lock;
  msg

(* Initializes RCB with a list of addresses [addrlst], where the current
   node sends and receives at address [i].
   Returns two closures for reading (deliver) and writing (broadcast) messages
   at address [i]. *)
let rcb_init (val_ser[@metavar]) (val_deser[@metavar]) addrlst i =
  let n = list_length addrlst in
  let vc = ref (vect_make n 0) in
  let seen = ref (vect_make n 0) in
  let inQueue : 'b inqueue Atomic.t = ref list_nil in
  let outQueues : 'a outqueues Atomic.t = ref (list_make n (queue_empty ())) in
  let lock = newlock () in
  let socket_handler = udp_socket () in
  let addr = unSOME (list_nth addrlst i) in
  socketBind socket_handler addr;
  fork (send_thread val_ser i socket_handler lock addrlst) outQueues;
  fork (recv_thread val_ser val_deser i socket_handler lock addrlst inQueue outQueues) seen;
  (deliver vc lock inQueue i, broadcast vc seen outQueues lock i)
