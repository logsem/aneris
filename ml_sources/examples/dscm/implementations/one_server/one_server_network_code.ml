open Ast
open Network_util_code
open Queue_code
open One_server_serialization_code

type 'a requestTy = ((((string * 'a, string) sumTy) * int) * saddr)
type 'a replyTy = ((((unit, 'a option) sumTy) * int) * saddr)


(* Fixme 1: Probably, two locks can be used, or even CAS operation. *)
(* Fixme 2: replace busy loop with some condition variable lib. *)

let receive_thread
    (val_ser[@metavar]) lk sh (inQ : 'a requestTy queue Atomic.t) =
  let rec loop () =
    let () =
      match receiveFrom sh with
      | None -> ()
      | Some msg ->
        let (event : 'a requestTy) =
          ((request_serializer val_ser).s_deser (fst msg), snd msg) in
        acquire lk;
        inQ := queue_add event !inQ;
        release lk
    in loop ()
  in loop ()

let send_reply
    (val_ser[@metavar] : 'a serializer) sh (reply_ev : 'a replyTy) =
  let (_reply, caddr) = reply_ev in
  let msg = (reply_serializer val_ser).s_ser (fst reply_ev) in
  ignore(sendTo sh msg caddr)

let send_thread (val_ser[@metavar] : 'a serializer) lk sh outQ =
  let rec loop () =
    (* At each step of the loop, process an event from the outQ, if any. *)
    if queue_is_empty !outQ
    then unsafe (fun () -> Unix.sleepf 0.5)
    else
      begin
        acquire lk;
        let tmp = !outQ in
        if not (queue_is_empty tmp)
        then
          begin
            let q = unSOME (queue_take_opt tmp) in
            let (event, outq) = q in
            outQ := outq;
            release lk;
            send_reply val_ser sh event
          end
        else release lk
      end;
    loop ();
  in loop ()

let init_network (val_ser[@metavar]) srv =
  let sh = socket PF_INET SOCK_DGRAM IPPROTO_UDP in
  let lk = newlock () in
  socketBind sh srv;
  let (inQ : 'a requestTy queue Atomic.t) = ref (queue_empty ()) in
  let (outQ : 'a replyTy queue Atomic.t) = ref (queue_empty ()) in
  fork (receive_thread val_ser lk sh) inQ;
  fork (send_thread val_ser lk sh) outQ;
  ((lk, inQ), outQ)
