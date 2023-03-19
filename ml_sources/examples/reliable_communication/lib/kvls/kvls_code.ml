open Ast
open Map_code
open Serialization_code
open Mt_server_code

(** ************************************************************* *)
(** ********************* SERVER SIDE *************************** *)
(** ************************************************************* *)

(** 1. The types of requests and replies *)

(** [Token * [Write(k,v) | Read(k)] |
    [Acquire() | Release(n) ]] *)
type 'a reqTy = (int * ((string * 'a, string) sumTy), (unit, int) sumTy) sumTy

(** [ RejectedReadOrWrite | [AcceptedWrite | AcceptedRead[None|(val, version)]]] |
    [ AcceptedAcquire     | [RejectedRelease | AcceptedRelease]] *)
type 'a repTy = (((unit, ('a * int) option) sumTy option), (int, unit option) sumTy) sumTy

(** Reply Events. *)
let rejected_access () : 'a repTy = InjL None
let accept_write () : 'a repTy = InjL (Some (InjL ()))
let accept_read  vo : 'a repTy = InjL (Some (InjR vo))
let granted tk : 'a repTy = InjR (InjL tk)
let rejected_release () : 'a repTy = InjR (InjR None)
let committed () : 'a repTy = InjR (InjR (Some ()))

(** Serializers *)
let write_serializer (val_ser[@metavar]) = prod_serializer string_serializer val_ser
let read_serializer = string_serializer
let kvs_serializer (val_ser[@metavar]) =
  prod_serializer int_serializer (sum_serializer (write_serializer val_ser) read_serializer)
let lock_serializer = sum_serializer unit_serializer int_serializer
let req_c2l_ser (val_ser[@metavar]) = sum_serializer (kvs_serializer val_ser) lock_serializer
let rep_l2c_ser (val_ser[@metavar]) =
  sum_serializer
    (option_serializer
       (sum_serializer unit_serializer (option_serializer (prod_serializer val_ser int_serializer))))
    (sum_serializer int_serializer (option_serializer unit_serializer))


(** The internal state of the server *)

(** 1. The main KVS (updated via commited transactions) *)
type 'a dbTy = ((string, ('a * int)) amap) Atomic.t

(** 2. The cache memory (current opened transaction).
    Simplification: there is only one global cache for all clients.
    Therefore, no concurrent accesses to disjoint keys) *)
type 'a cacheTy = ((string, 'a) amap) Atomic.t

(** 3. Lease. Lease is a global Mutex.t that comes with a monotonicaly growing token
    and a lease status indicating whether a lease is currently given to a client. *)
type leaseTy = Mutex.t
type tokenTy = int Atomic.t
type leaseStatusTy = bool Atomic.t



(** State Transition System of serving a client:

WHILE (true) DO {

   (* ----------------------- STATE 0: WAIT ON OPENED CONNECTION ----------------------- *)
   WHILE (no request to open transaction is received)
   DO { True };


   (* ----------------------- STATE 1: OPEN TRANSACTION -------------------------------- *)
   (* The next request is recieved, guaranteed to be acquire request by the client side *)
   acquire lease;
   leaseStatus := true;

   (* ----------------------- STATE 2: PROCESS TRANSACTION ----------------------------- *)
   WHILE (transaction is active AND next request is a valid read OR write request)
   DO { process the request with RW-access cache and RO-access storage
        and send a valid reply };

   (* ----------------------- STATE 3: CLOSE TRANSACTION ------------------------------- *)
   leaseStatus := false;
    token := !token + 1;
    IF THEN ELSE;
   cache := map_empty ();
   release lease;

   IF next request is a valid release request THEN send valid reply
   ELSE send rejected

} *)


(** Acquire and Relase Actions. *)
let grant_lease lease leaseStatus token () : 'a repTy =
  acquire lease;
  leaseStatus := true;
  granted !token

let getback_lease
    (lease : leaseTy) (leaseStatus : leaseStatusTy) ( token : tokenTy)
    (cache : 'a cacheTy)  (db : 'a dbTy) (commit_flag : bool)
  : 'a repTy option =
  leaseStatus := false;
  token := !token + 1;
  let rep_opt =
    if commit_flag
    then
      let n = !token in
      map_iter (fun k v -> db := map_insert k (v,n) !db) !cache;
      Some (committed ())
    else None in
  cache := map_empty ();
  release lease;
  rep_opt


(** Processes the request event (request & the reply cell). *)
let client_request_handler
    (lease : leaseTy) (leaseStatus : leaseStatusTy) (token : tokenTy)
    (cache : 'a cacheTy) (db : 'a dbTy)
    (reqo : 'a reqTy option) : 'a repTy option =
  let res =
    match reqo with

    (* TIMEOUT ON LISTENING *)
    | None ->
      if !leaseStatus
      then getback_lease lease leaseStatus token cache db false
      else None

    (* RECEIVING A NEW REQUEST *)
    | Some req ->

      match req with
      (* ACQUIRE OR RELEASE REQUEST *)
      | InjR r ->
        begin match r with

          (* ACQUIRE REQUEST *)
          | InjL _acq -> Some (grant_lease lease leaseStatus token ())

          (* RELEASE REQUEST *)
          | InjR release_tk ->
            if release_tk = !token
            then getback_lease lease leaseStatus token cache db true
            else
              (* Note how we don't need to change the server state because it was done previously *)
              Some (rejected_release ())
        end

      (* WRITE OR READ REQUEST *)
      | InjL dbreq ->
        let (tk, req) = dbreq in
        if not (tk = !token)
        then Some (rejected_access ())
        else match req with

          (* WRITE REQUEST *)
          | InjL p ->
            let (k, v) = p in
            cache := map_insert k v !cache;
            Some (accept_write ())

          (* READ REQUEST *)
          | InjR k ->
            let vo =
              (* First we lookup in cache, then in the main storage. *)
              match map_lookup k !cache with
              | None -> map_lookup k !db
              | Some v -> Some (v, tk)
            in Some (accept_read vo)
  in res

(** Initialization of the leader-followers database. *)
let start_server_processing_clients (ser[@metavar]) addr lease leaseStatus token cache db () =
  run_server_opt (rep_l2c_ser ser) (req_c2l_ser ser) addr
    (fun req -> client_request_handler lease leaseStatus token cache db req)

let init_server (ser[@metavar] : 'a serializer) addr : unit =
  let (db : 'a dbTy) = ref (map_empty ()) in
  let (cache : 'a cacheTy) = ref (map_empty ()) in
  let (lease : leaseTy) = newlock () in
  let (leaseStatus : leaseStatusTy) = ref false in
  let (token : tokenTy) = ref 0 in
  fork (start_server_processing_clients ser addr lease leaseStatus token cache db) ()


(** ************************************************************* *)
(** ********************* CLIENT SIDE *************************** *)
(** ************************************************************* *)

(** The client's internal state consist of token and the channel.
    This state is hidden from the user in the request closures. *)

(** THE CLIENT'S API :
    init_client_proxy :
    'a serializer ->
    saddr ->
    saddr ->
    ((unit -> int) *
     (unit -> unit option)) *
    ((string -> 'a -> unit option) *
    (string -> ('a * int) option))
 *)

(** Open transaction only if not already opened. *)
let acquire_request tk rpc =
  match !tk with
    | None -> make_request rpc (InjR (InjL ()))
    | Some _abs -> assert false

(** Make transaction request only if transaction is opened and active. *)
let active_request rpc tk req =
  match !tk with
  | None -> assert false
  | Some n -> make_request rpc (req n)

let init_client_proxy (ser[@metavar]) clt_addr srv_addr =
 let rpc = init_client_proxy (req_c2l_ser ser) (rep_l2c_ser ser) clt_addr srv_addr in
 let tk = ref None in
 let acquire_dlock () : int =
   match acquire_request tk rpc with
   | InjL _abs -> assert false
   | InjR ar ->
     match ar with
     | InjL n -> tk := Some n; n (* Open and mark transaction as active. *)
     | InjR _abs -> assert false
 in
 let release_dlock () : unit option =
   match active_request rpc tk (fun n -> (InjR (InjR n))) with
   | InjL _abs -> assert false
   | InjR ar ->
     match ar with
     | InjL _abs -> assert false
     (* Mark transaction as closed and inactive due to reject or closing it. *)
     | InjR opt -> tk := None; opt
 in
 let write k v : unit option =
   match active_request rpc tk (fun n -> InjL (n, InjL (k, v))) with
     | InjR _abs -> assert false
     | InjL wro ->
       match wro with
       | None -> tk := None; None (* Abort transaction. *)
       | Some wr ->
         match wr with
         | InjL _uo -> Some ()
         | InjR _abs -> assert false
 in
 let read k : ('a * int) option =
   match active_request rpc tk (fun n -> InjL (n, (InjR k))) with
     | InjR _abs -> assert false
     | InjL wro ->
       match wro with
       | None -> tk := None; None (* Abort transaction. *)
       | Some wr ->
         match wr with
         | InjL _abs -> assert false
         | InjR ro -> ro
 in ((acquire_dlock, release_dlock), (write, read))



let node0 clt_addr db_addr =
  let db_funs = init_client_proxy int_serializer clt_addr db_addr in
  let ((acquire_dl, release_dl), (write, _rd)) = db_funs in
  let _n = acquire_dl () in
  match write "x" 37 with
  | None -> false
  | Some () ->
    match write "y" 1 with
    | None -> false
    | Some () ->
      match release_dl () with
      | None -> false
      | Some () -> true

let node1 clt_addr db_addr =
  let db_funs = init_client_proxy int_serializer clt_addr db_addr in
  let ((acquire_dl, release_dl), (_write, read)) = db_funs in
  let rec loop () =
    let _m = acquire_dl () in
    match read "x" with
    | None -> false
    | Some vxn ->
      let (vx, nx) = vxn in
      if vx = 37
      then
        match read "y" with
        | None -> false
        | Some vyn ->
          let (vy, ny) = vyn in
          assert (vy = 1 && nx = ny);
          let _op = release_dl () in true
      else
      begin
        let _op = release_dl () in
        unsafe (fun () -> Unix.sleepf 2.0);
        loop ()
      end
  in loop ()
