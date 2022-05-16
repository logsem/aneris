open Ast
open One_server_serialization_code

(* TODO: check and explain the code. *)
let wait_for_reply (val_ser[@metavar]) srv sh reqId reqMsg =
  let rid = !reqId in
  let rec aux () =
    match receiveFrom sh with
      None -> ignore(sendTo sh reqMsg srv); aux ()
    | Some rply ->
      let repl = (reply_serializer val_ser).s_deser (fst rply) in
      let (res, resId) = repl in
      assert (resId <= rid);
      if resId = rid
      then
        begin
          reqId := rid + 1;
          res
        end
      else aux ()
  in aux ()

  let request (val_ser[@metavar]) srv sh lock reqId req =
    (* Use lock to prevent client to run requests in parallel. *)
    acquire lock;
    let reqMsg =
      (request_serializer val_ser).s_ser (req, !reqId) in
    ignore(sendTo sh reqMsg srv);
    let r = wait_for_reply val_ser srv sh reqId reqMsg in
    release lock;
    r

let install_proxy (val_ser[@metavar]) srv caddr =
  let sh = socket PF_INET SOCK_DGRAM IPPROTO_UDP in
  let reqId = ref 0 in
  socketBind sh caddr;
  setReceiveTimeout sh 3 0;
  let lock = newlock () in
  let wr k v = request (val_ser[@metavar]) srv sh lock reqId (InjL (k, v)) in
  let rd k   = request (val_ser[@metavar]) srv sh lock reqId (InjR k) in
  (wr, rd)
