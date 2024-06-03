open Ast
open List_code
open Map_code
open Network_util_code
open Serialization_code
open Mt_server_code


(** The internal state of the server *)

(** 1. The KVS type (updated via commited transactions) *)
type 'a kvsTy = ((string, ((string * ('a * int)) alist)) amap)

(** 2. The last transaction id and the list of transaction
      timestamps and wether they are active or not *)
type trsTy = (int * ((int * bool) alist))

(** 3. The cache memory (current opened transaction).
    Simplification: there is only one global cache for all clients.
    Therefore, no concurrent accesses to disjoint keys) *)
type 'a cacheTy = ((string, 'a) amap)
type 'a reqTy = ((string * int), (unit, int * 'a cacheTy) sumTy) sumTy
type 'a replTy = ('a option, (trsTy, bool) sumTy) sumTy
type 'a connection_state =
  (saddr * (Mutex.t *
   (('a reqTy, 'a replTy) rpc *
    ((int * 'a cacheTy Atomic.t) option Atomic.t))))

(** Serializers *)
let req_ser (val_ser[@metavar]) =
  sum_serializer
    (prod_serializer string_serializer int_serializer)
    (sum_serializer
       unit_serializer
       (prod_serializer
          int_serializer
          (list_serializer (prod_serializer string_serializer val_ser))))

let repl_ser (val_ser[@metavar]) =
  sum_serializer
    (option_serializer val_ser)
    (sum_serializer
       (prod_serializer
          int_serializer
          (list_serializer (prod_serializer int_serializer bool_serializer))
        )
       bool_serializer)

let kvs_get k kvs =
  match map_lookup k kvs with
  | None -> list_nil
  | Some vlst -> assert (not (vlst = None)); vlst

let kvs_get_last kt (kvs : 'a kvsTy) : 'a option =
  let (k, t) = kt in
  let rec aux l =
    match l with
    | None -> None
    | Some p ->
      let ((_k, (v, tv)), tl) = p in
      if tv = t then assert false
      else if tv < t then Some v
      else aux tl
  in aux (kvs_get k kvs)

let update_kvs (kvs : 'a kvsTy) (cache : 'a cacheTy) (tc : int)
  : 'a kvsTy =
  let rec upd kvs_t cache_t =
    match cache_t with
    | None -> kvs_t
    | Some chl ->
      let (kv, cache_l) = chl in
      let (k,v) = kv in
      let vlst = kvs_get k kvs in
      let newval = (k, (v, tc)) in
      let newvals = (list_cons newval vlst) in
      let kvs_t' = map_insert k newvals kvs_t in
      upd kvs_t' cache_l
  in upd kvs cache

let update_transaction_list (uts : int) (trs : trsTy Atomic.t) =
  let (ts, trs_list) = !trs in
  let rec upd l  =
    match l with
    | None -> list_nil
    | Some p ->
      let (transaction, list) = p in
      let (t, b) = transaction in
      if t != uts then list_cons (t, b) (upd list)
      else list_cons (t, false) list
  in ts, upd trs_list


let check_at_key (ts : int) (tc : int) (vlst : ((string * ('a * int)) alist)) =
  assert (ts < tc);
  match vlst with
  | None -> true
  | Some l ->
    let (vlast, _hd) = l in
    let ((_k, (_v, t))) = vlast in
    if tc <= t || t = ts then assert false
    else t < ts

let garbage_collection (kvs : 'a kvsTy Atomic.t) (trs : trsTy Atomic.t) : 'a kvsTy =
  ignore trs; !kvs

let commit_handler
    (kvs : 'a kvsTy Atomic.t)
    (cdata : int * 'a cacheTy)
    (trs : trsTy Atomic.t) () =
  let (vnum, _) = !trs in
  let tc = vnum + 1 in
  let kvs_t = !kvs in
  let (ts, cache) = cdata in
  trs := update_transaction_list ts trs;
  if list_is_empty cache
  then true
  else
    let b = map_forall
        (fun k _v ->
           let vlsto = (map_lookup k kvs_t) in
           let vs = if vlsto = None then list_nil else unSOME vlsto in
           check_at_key ts tc vs) cache in
    if b then begin
      kvs := update_kvs kvs_t cache tc;
      kvs := garbage_collection kvs trs;
      true
    end
    else false

let lk_handle lk handler =
  acquire lk;
  let res = handler () in
  release lk;
  res

let read_handler (kvs : 'a kvsTy Atomic.t) tk () =
  kvs_get_last tk !kvs

let start_handler (trs : trsTy Atomic.t) () =
  let (ts, trs_l) = !trs in
  let vnext = ts + 1 in
  let trs_l_next = list_cons (vnext, true) trs_l in
  trs := (vnext, trs_l_next);
  !trs

let client_request_handler
    (lk : Mutex.t) (kvs : 'a kvsTy Atomic.t)
    (trs : trsTy Atomic.t) (req : 'a reqTy)
  : 'a replTy =
  let res =
    match req with
    (* READ request *)
    | InjL tk ->
      InjL (lk_handle lk (read_handler kvs tk))
    (* START or COMMIT request *)
    | InjR r ->
      begin match r with
        (* START request *)
        | InjL _tt ->
          InjR (InjL (lk_handle lk (start_handler trs)))
        (* COMMIT request *)
        | InjR cdata ->
          InjR (InjR (lk_handle lk (commit_handler kvs cdata trs)))
      end
  in res

let start_server_processing_clients (ser[@metavar]) addr lk kvs trs () =
  run_server (repl_ser ser) (req_ser ser) addr
    (fun req -> client_request_handler lk kvs trs req)

let init_server (ser[@metavar] : 'a serializer) addr : unit =
  let (kvs : 'a kvsTy Atomic.t) = ref (map_empty ()) in
  let (trs : trsTy Atomic.t) = ref (0, list_nil) in
  let (lk : Mutex.t) = newlock () in
  fork (start_server_processing_clients ser addr lk kvs trs) ()


let init_client_proxy (ser[@metavar]) clt_addr srv_addr : 'a connection_state =
  let rpc = init_client_proxy (req_ser ser) (repl_ser ser) clt_addr srv_addr in
  let txt = ref None in
  let lk = newlock () in
  (clt_addr, (lk, (rpc, txt)))

let start (cst : 'a connection_state) : unit =
  let (_clt_addr, (lk, (rpc, tst))) = cst in
  acquire lk;
  begin
    match !tst with
    | Some _abs -> assert false
    | None ->
      let repl = make_request rpc (InjR (InjL ())) in
      match repl with
      | InjL _abs -> assert false
      | InjR s ->
        match s with
        | InjL trs ->
          let (ts, _) = trs in
          tst := Some (ts, ref (map_empty ()))
        | InjR _abs -> assert false
  end;
  release lk

let read (cst : 'a connection_state) k : 'a option =
  let (_clt_addr, (lk, (rpc, tst))) = cst in
  acquire lk;
  let vo =
    match !tst with
    | None -> assert false
    | Some st ->
      let (ts, cache) = st in
      match map_lookup k !cache with
      | Some v -> Some v
      | None ->
        let repl = make_request rpc (InjL (k, ts)) in
        match repl with
        | InjL vo -> vo
        | InjR _abs -> assert false
  in release lk; vo

let write (cst : 'a connection_state) k v : unit =
  let (_clt_addr, (lk, (_rpc, tst))) = cst in
  acquire lk;
  match !tst with
  | None -> assert false
  | Some st ->
    let (_ts, cache) = st in
    cache := map_insert k v !cache;
    release lk

let commit (cst : 'a connection_state) : bool =
  let (_clt_addr, (lk, (rpc, tst))) = cst in
  acquire lk;
  let b =
    match !tst with
    | None -> assert false
    | Some st ->
      let (ts, cache) = st in
      let repl =
        let cch = !cache in
        if cch = None then InjR (InjR true)
        else make_request rpc (InjR (InjR (ts, cch))) in
      match repl with
      | InjL _abs -> assert false
      | InjR r ->
        match r with
        | InjL _abs -> assert false
        | InjR b ->
          tst := None; b
  in release lk; b
