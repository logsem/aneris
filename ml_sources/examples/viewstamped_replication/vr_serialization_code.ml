open Ast
open List_code
open Serialization_code

type 'a requestTy = (((string * 'a, string) sumTy * saddr) * int)
type 'a replyTy = (((int * int) * 'a option) * saddr)
type 'a prpTy = (((int * 'a requestTy) * int) * int)
type cmtTy = (int * int)
type pokTy = ((int * int) * int)
type svcTy = (int * int)
type 'a dvcTy =  (((((int * 'a requestTy alist) * int) * int) * int) * int)
type 'a snvTy = (((int * 'a requestTy alist) * int) * int)
type gstTy = ((int * int) * int)
type 'a nstTy = ((((int * 'a requestTy alist) * int) * int) * int)
type 'a msgTy =
  ((
      ('a prpTy,   (* prepare *)
       cmtTy       (* commit *)
      ) sumTy,
      (pokTy,      (* prepareOK *)
       svcTy       (* startViewChange *)
      ) sumTy
    ) sumTy,
      (('a dvcTy,  (* doViewChange *)
        'a snvTy   (* startNewView *)
       ) sumTy,
       (gstTy,     (* getState *)
        'a nstTy   (* newState *)
       ) sumTy
      ) sumTy
    ) sumTy

type 'a msgInTy =
  ('a msgTy, 'a requestTy) sumTy

type 'a msgOutTy =
  ('a msgTy, 'a replyTy) sumTy

(** Serialization *)

let clntId_serializer = saddr_serializer
let nodeId_serializer = int_serializer
let seqId_serializer = int_serializer

let write_serializer (val_ser[@metavar]) = prod_serializer string_serializer val_ser

let read_serializer = string_serializer

let rslt_serializer (val_ser[@metavar]) = option_serializer val_ser

let view_serializer = int_serializer
let cmt_num_serializer = int_serializer
let op_num_serializer = int_serializer

(* ⟨REQUEST op, c, s⟩ *)

let request_serializer (val_ser[@metavar]) : 'a requestTy serializer =
  prod_serializer
    (prod_serializer
       (sum_serializer (write_serializer val_ser) read_serializer)
       clntId_serializer)
    seqId_serializer

(* ⟨REPLY v, s, x, c⟩ *)
let reply_serializer (val_ser[@metavar]) : 'a replyTy serializer =
  prod_serializer
    (prod_serializer
       (prod_serializer view_serializer seqId_serializer)
       (rslt_serializer val_ser))
    clntId_serializer

let log_serializer (val_ser[@metavar]) = list_serializer (request_serializer val_ser)

(* ⟨PREPARE v, m, n, k⟩ *)
let prp_serializer (val_ser[@metavar]) : 'a prpTy serializer =
  prod_serializer
    (prod_serializer
       (prod_serializer view_serializer (request_serializer val_ser))
       op_num_serializer)
    cmt_num_serializer

(* ⟨COMMIT v, k⟩ *)
let cmt_serializer : cmtTy serializer = prod_serializer view_serializer cmt_num_serializer

(* ⟨PREPAREOK v, n, i⟩ *)
let pok_serializer : pokTy serializer =
  prod_serializer
    (prod_serializer view_serializer op_num_serializer)
    nodeId_serializer

(* ⟨STARTVIEWCHANGE v, i⟩ *)
let svc_serializer :  svcTy serializer = prod_serializer view_serializer nodeId_serializer

(* ⟨DOVIEWCHANGE v, l, v’, n, k, i⟩ *)
let dvc_serializer (val_ser[@metavar]) : 'a dvcTy serializer =
  prod_serializer
    (prod_serializer
       (prod_serializer
          (prod_serializer
             (prod_serializer view_serializer (log_serializer val_ser))
             view_serializer)
          op_num_serializer)
       cmt_num_serializer)
    nodeId_serializer

(* ⟨STARTVIEW v, l, n, k⟩ *)
let snv_serializer (val_ser[@metavar]) : 'a snvTy serializer =
  prod_serializer
    (prod_serializer
       (prod_serializer view_serializer (log_serializer val_ser))
       op_num_serializer)
    cmt_num_serializer

(* ⟨GETSTATE v, n’, i⟩ *)
let gst_serializer : gstTy serializer =
  prod_serializer
    (prod_serializer view_serializer op_num_serializer)
    nodeId_serializer

(* ⟨NEWSTATE v, l, n, k, i⟩ *)
let nst_serializer (val_ser[@metavar]) : 'a nstTy serializer =
  prod_serializer
    (prod_serializer
       (prod_serializer
          (prod_serializer view_serializer (log_serializer val_ser))
          op_num_serializer)
       cmt_num_serializer)
    nodeId_serializer

let msg_serializer (val_ser[@metavar]) : 'a msgTy serializer =
  sum_serializer
    (sum_serializer
       (sum_serializer (prp_serializer val_ser) cmt_serializer)
       (sum_serializer  pok_serializer svc_serializer))
    (sum_serializer
       (sum_serializer (dvc_serializer val_ser) (snv_serializer val_ser))
       (sum_serializer  gst_serializer (nst_serializer val_ser)))

let msgIn_serializer (val_ser[@metavar] : 'a serializer) : 'a msgInTy serializer =
  sum_serializer
    (msg_serializer val_ser)
    (request_serializer val_ser)

let msgOut_serializer (val_ser[@metavar] : 'a serializer) : 'a msgOutTy serializer =
  sum_serializer
    (msg_serializer val_ser)
    (reply_serializer val_ser)

(** Smart constructors for messages *)

let prp v op n k = (InjL (InjL (InjL (((v, op), n), k))))

let cmt v k = (InjL (InjL (InjR (v, k))))

let pok v n i = (InjL (InjR (InjL ((v, n), i))))

let svc v i = (InjL (InjR (InjR (v, i))))

let dvc v l v' n k i =  (InjR (InjL (InjL (((((v, l), v'), n), k), i))))

let snv v l n k = (InjR (InjL (InjR (((v, l), n), k))))

let gst v n i = (InjR (InjR (InjL ((v, n), i))))

let nst v l n k j = (InjR (InjR (InjR (((((v, l), n), k), j)))))

let req op c s =  ((op, c), s)

let rpl v s x c = (((v, s), x), c)
