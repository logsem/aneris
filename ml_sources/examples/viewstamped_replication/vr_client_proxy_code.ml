open Ast
open List_code
open Network_util_code
open Vr_serialization_code

(* TODO: check and explain the code. *)
let wait_for_reply (val_ser[@metavar]) len saddrl sh reqId prmId reqMsg =
  let rid = !reqId in
  let rec aux () =
    match receiveFrom sh with
      None ->
      sendto_all_set sh saddrl reqMsg;
      aux ()
    | Some rply ->
      let repl = (reply_serializer val_ser).s_deser (fst rply) in
      let (((v, resId), res), _caddr) = repl in
      assert (resId <= rid);
      if resId = rid
      then
        begin
          prmId := v mod len;
          reqId := rid + 1;
          res
        end
      else aux ()
  in aux ()

let make_request (val_ser[@metavar]) len saddrl caddr sh lock reqId prmId =
  let request req =
    (* Use lock to prevent client to run requests in parallel. *)
    acquire lock;
    let dst = unSOME (list_nth saddrl !prmId) in
    let reqMsg = (request_serializer val_ser).s_ser (((req, caddr), !reqId)) in
    ignore(sendTo sh reqMsg dst);
    unsafe (fun () -> Printf.eprintf "made request: %s\n%!" (reqMsg));
    let r = wait_for_reply val_ser len saddrl sh reqId prmId reqMsg in
    release lock; r
  in
  let wr k v =
    let _req = request (InjL (k, v)) in () in
  let rd k =
    request (InjR k) in
  (wr, rd)

(* TODO: check and explain the code. *)
let install_proxy (val_ser[@metavar]) saddrl caddr =
  let sh = socket PF_INET SOCK_DGRAM IPPROTO_UDP in
  let lock = newlock () in
  let prmId = ref 0 in
  let reqId = ref 0 in
  let len = list_length saddrl in
  setReceiveTimeout sh 3 0;
  socketBind sh caddr;
  make_request val_ser len saddrl caddr sh lock reqId prmId
