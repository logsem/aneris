open Ast
open Map_code
open List_code
open Serialization_code
open Mt_server_code

(* This is an implementation of the multiversion timestamp concurrency 
   control algorithm presented in chapter 5 of Concurrent Control and 
   Recovery in Database Systems by Bernstein et. al. *)

(** ************************************************************* *)
(** ********************* SERVER SIDE *************************** *)
(** ************************************************************* *)

(** The types of requests and replies *)

(** [ Start  | [ Timestamp * [ Write(k,v) | [ Read(k) | Commit() ] ] ] ] *)
type 'a reqTy = (unit, int * ((string * 'a, (string, unit) sumTy) sumTy)) sumTy

(** [ Abort | [ Accept | [ AcceptRead(v) | AcceptStart(ts) ] ] ] *)
type 'a repTy = (unit, (unit, ('a option, int) sumTy) sumTy) sumTy

(** Request Events *)
let start_req () : 'a reqTy = InjL ()
let write_req ts k v : 'a reqTy = InjR (ts, InjL (k, v))
let read_req ts k : 'a reqTy = InjR (ts, InjR (InjL k))
let commit_req ts : 'a reqTy = InjR (ts, InjR (InjR ()))

(** Reply Events *)
let abort_rep () : 'a repTy = InjL ()
let accept_rep () : 'a repTy = InjR (InjL ())
let accept_read_rep v : 'a repTy = InjR (InjR (InjL v))
let accept_start_rep ts : 'a repTy = InjR (InjR (InjR ts)) 

(** Serializers *)
let write_serializer (val_ser[@metavar]) = prod_serializer string_serializer val_ser
let read_serializer = string_serializer
let start_serializer = unit_serializer
let commit_serializer = unit_serializer
let timestamp_serializer = int_serializer
let req_c2l_ser (val_ser[@metavar]) = sum_serializer
                                      start_serializer
                                      (prod_serializer 
                                        timestamp_serializer 
                                        (sum_serializer 
                                          (write_serializer val_ser)
                                          (sum_serializer 
                                            read_serializer
                                            commit_serializer)))

let abort_serializer = unit_serializer
let accept_serializer = unit_serializer
let accept_read_serializer (val_ser[@metavar]) = option_serializer val_ser
let accept_start_serializer = int_serializer
let rep_l2c_ser (val_ser[@metavar]) = sum_serializer 
                                        abort_serializer
                                        (sum_serializer
                                          accept_serializer
                                          (sum_serializer
                                            (accept_read_serializer val_ser)
                                            accept_start_serializer))

(** The internal state of the server *)

(** The main KVS supporting multiple versions of the data 
    attached with the write timestamp and largest read timestamp *)
type 'a dbTy = ((string, ('a option * (int * int)) alist) amap) Atomic.t

(** Commit map mapping transaction timestamps to commit information. 
    - The bool indicates wheter the transaction has commited yet, 
      false is for in progress, true for commit and if a transaction aborts it gets removed 
    - The first list is a list of keys written to by the transaction. 
      This is used when a transaction aborts and its entries must be deleted.
    - The second list is a list of timestamps the transaction has read from. 
      This is used to check wheter a transaction can commit since it can only
      commit if all transaction it has read from also commited. *)
type cmTy = ((int, (bool * ((string alist) * (int alist)) )) amap) Atomic.t

(** Timestamp given to incomming transactions *)
type tsTy = int Atomic.t

(* Lock for ensuring serial access to the datastructures *)
type lockTy = Mutex.t

(** Request handling *)

let start tsCounter (cm : cmTy) () = 
  let ret = !tsCounter in
  tsCounter := !tsCounter + 1;
  cm := map_insert ret (false, (None, None)) !cm; 
  Some (accept_start_rep ret)

let rec index_elem_leq_ts' (l : ('a * (int * int)) alist) ts i res () =
  match l with 
  | Some a ->
    let (vo, (wts, rts)) = (fst a) in  
    if wts < ts then (
      index_elem_leq_ts' (snd a) ts (i+1) (Some (i, (vo, (wts, rts)))) ()
    ) else ( 
      res
    )  
  | None -> res
  
(* Find the greatest element i in the list l less than ts (with respect to write-timestamp (wts)) and 
also returns the index of this element. Returns None if ts is the smallest timestamp 
(also in the case where l is empty) *)    
let index_elem_leq_ts (l : ('a * (int * int)) alist) ts () = index_elem_leq_ts' l ts 0 None ()

let rec list_insert l i v = 
  match l with 
  | Some (h, t) ->
    if i <= 0 then 
      Some (h, Some (v, t))
    else 
      Some (h, list_insert t (i-1) v)
  | None -> Some (v, None)

let updateRollbackDependency ts k cm = 
  match (map_lookup ts !cm) with 
  | Some (b, (keys, timestamps)) ->
    let updatedKeysList = list_append keys (Some (k, None)) in 
    cm := map_insert ts (b, (updatedKeysList, timestamps)) !cm
  | None -> assert false

(* Removes for each key in keys all the entries with write-timestamp equal to ts in the database db *)  
let rollback_commit ts keys db =
  let handlerFun k =  
    match map_lookup k !db with 
    | Some l -> 
      let filterFun (_, (wts, _)) = 
        if wts = ts then true else false
      in 
      let l' = list_filter filterFun l in 
      db := map_insert k l' !db
    | None -> assert false
  in
  list_iter handlerFun keys

let abort_transaction ts cm db = 
  match map_lookup ts !cm with 
  | Some (_, (keys, _)) ->
    cm := map_remove ts !cm;
    rollback_commit ts keys db; 
  | None -> assert false

let write ts k v (db : 'a dbTy) cm () =
  match map_lookup k !db with
  (* nothing has been written to key k yet, we insert our version *)
  | None ->  
    db := map_insert k (Some ((Some v, (ts, ts)), None)) !db;
    updateRollbackDependency ts k cm;
    Some (accept_rep ())
  | Some l ->  
    (* we look up the version we must come after *)
    match index_elem_leq_ts l ts () with
    | Some (i, (_, (_, rts))) ->
      (* we came too late and must abort the write and the whole transaction *)
      if ts < rts then (
        abort_transaction ts cm db;
        Some (abort_rep ())
      (* we are in time and can add our new version *)  
      ) else (
        let updatedList = list_insert l i (Some v, (ts, ts)) in 
        db := map_insert k updatedList !db;
        updateRollbackDependency ts k cm;
        Some (accept_rep ())
      )  
    (* we are the earliest version or the only version and have nothing to violate *)  
    | None -> 
      let updatedList = Some ((Some v, (ts, ts)), l) in
      db := map_insert k updatedList !db;
      updateRollbackDependency ts k cm;
      Some (accept_rep ())

let updateCommitDependency ts ws cm = 
  match (map_lookup ts !cm) with 
  | Some (b, (keys, timestamps)) ->
    let updatedTimestampsList = list_append timestamps (Some (ws, None)) in 
    cm := map_insert ts (b, (keys, updatedTimestampsList)) !cm
  | None -> assert false

let updateReadTimestamp l i vo wts ts db k =
  let updatedList = list_update l i (vo, (wts, ts)) in 
  db := map_insert k updatedList !db

let read ts k db cm () = 
  match map_lookup k !db with
  (* nothing has been written to key k yet, so we read the initial value 
     None and give it our timestamp *)
  | None -> 
    let updatedList = Some((None, (-1, ts)), None) in
    db := map_insert k updatedList !db;
    Some (accept_read_rep None)
  | Some l -> 
    (* we lock up the version we must read *)
    match index_elem_leq_ts l ts () with
    | Some (i, (vo, (wts, rts))) ->
      updateCommitDependency ts wts cm;
      (* we are the largest timestamp having read this version and must update rts to reflect this *)
      if rts < ts then (
        updateReadTimestamp l i vo wts ts db k;
        Some (accept_read_rep vo)
        ) 
      else (
        Some (accept_read_rep vo)
      )
    (* We have a smaller timestamp than all of the writes. In this case we read
        the initial value (None) and update it with our timestamp. *)  
    | None ->
      let updatedList = Some((None, (-1, ts)), l) in
      db := map_insert k updatedList !db;
      Some (accept_read_rep None)

let abort_test timestamps cm = 
  let testFun = (fun ts -> map_mem ts !cm) in 
  list_forall testFun timestamps 

let ready_to_commit_test timestamps cm = 
  let testFun = (fun ts -> match (map_lookup ts !cm) with | Some (b, _) -> b | None -> assert false) in 
  list_forall testFun timestamps

let commit ts cm db () = 
  match map_lookup ts !cm with 
  | Some (_, (keys, timestamps)) ->
    (match abort_test timestamps cm with 
    | true -> 
      (match ready_to_commit_test timestamps cm with 
      | true -> 
        cm := map_insert ts (true, (keys, timestamps)) !cm; 
        Some (accept_rep ())
      (* This is the wait case, it has not yet been decided wheter we can commit yet *)
      | false -> None)
    | false -> 
      cm := map_remove ts !cm;
      rollback_commit ts keys db; 
      Some (abort_rep ()))
  | None -> assert false

(** Processes the request event. *)
let client_request_handler
    (tsCounter : tsTy) 
    (db : 'a dbTy) 
    (cm : cmTy) 
    (lock: lockTy)
    (reqo : 'a reqTy option) : 'a repTy option =
  let res =
    match reqo with
    (* TIMEOUT ON LISTENING *)
    | None -> None
    (* RECEIVING A NEW REQUEST *)
    | Some req ->
      match req with 
      (* START REQUEST *)
      | InjL () -> 
        acquire lock;
        let res = start tsCounter cm () in 
        release lock;
        res
      (* WRITE REQUEST OR READ REQUEST OR COMMIT REQUEST *)
      | InjR (ts, req') ->
        match req' with
        (* WRITE REQUEST *)
        | InjL (k, v) -> 
          acquire lock;
          let res = write ts k v db cm () in 
          release lock;
          res
        (* READ REQUEST OR COMMIT REQUEST *)
        | InjR req'' ->
          match req'' with 
          (* READ REQUEST *)
          | InjL k -> 
            acquire lock;
            let res = read ts k db cm () in 
            release lock;
            res
          (* COMMIT REQUEST *)
          | InjR () -> 
            let rec commit_wait () = 
              acquire lock;
              let temp_res = commit ts cm db () in
              release lock;
              match temp_res with 
              (* we know wheter the transaction can commit or must abort*)
              | Some a -> Some a
              (* it can't yet  be decied wheter the transaction can commit, so we try again*)
              | None -> commit_wait () 
            in 
            commit_wait ()
  in res

(** Initialization of the database. *)
let start_server_processing_clients (ser[@metavar]) addr tsCounter db cm lock () =
  run_server_opt (rep_l2c_ser ser) (req_c2l_ser ser) addr
    (fun req -> client_request_handler tsCounter db cm lock req)

let init_server (ser[@metavar] : 'a serializer) addr () : unit =
  let (tsCounter : tsTy) = ref 0 in
  let (db : 'a dbTy) = ref (map_empty ()) in
  let (cm : cmTy) = ref (map_empty ()) in
  let (lock : lockTy) = newlock () in
  fork (start_server_processing_clients ser addr tsCounter db cm lock) ()


(** ************************************************************* *)
(** ********************* CLIENT SIDE *************************** *)
(** ************************************************************* *)

(** Start transaction only if not already started. *)
  let start_request ts rpc =
    match !ts with
    | None -> make_request rpc (start_req ())
    | Some _ -> assert false

(** Make transaction request only if transaction is started. *)
  let active_request rpc ts req =
    match !ts with
    | None -> assert false
    | Some n -> make_request rpc (req n)

(* Function for initializing client connections. Each client can intialize multiple 
   connections but can only execute one transactions at a time on a single connection *)
let init_client_proxy (ser[@metavar]) clt_addr srv_addr =
 let rpc = init_client_proxy (req_c2l_ser ser) (rep_l2c_ser ser) clt_addr srv_addr in
 let ts = ref None in (* Client session state i.e. the transaction currently executing *)
 let lock = newlock () in (* Lock for serializing concurrent client envocations *)
 let start () : unit =
  acquire lock;
  match start_request ts rpc with 
    (* ABORT *)
    | InjL () -> assert false
    (* ACCEPT OR ACCEPT_READ OR ACCEPT_START *)   
    | InjR rep' ->  
      match rep' with
      (* ACCEPT *)
      | InjL () -> assert false
      (* ACCEPT_READ OR ACCEPT_START *)   
      | InjR rep'' ->
        match rep'' with
        (* ACCEPT_READ *) 
        | InjL _ -> assert false
        (* ACCEPT_START *)  
        | InjR i -> 
          ts := Some i;
          release lock
 in
 let commit () : unit option =
    acquire lock;
    match active_request rpc ts (fun n -> commit_req n) with
    (* ABORT *)
    | InjL () -> ts := None; release lock; None
    (* ACCEPT OR ACCEPT_READ OR ACCEPT_START *)   
    | InjR rep' ->  
      match rep' with
      (* ACCEPT *)
      | InjL () -> ts := None; release lock; Some ()
        (* ACCEPT_READ OR ACCEPT_START *)   
      | InjR _ -> assert false
 in
 let write k v : unit option =
    acquire lock;
    match active_request rpc ts (fun n -> write_req n k v) with
    (* ABORT *)
    | InjL () -> 
      ts := None; 
      release lock; 
      None
    (* ACCEPT OR ACCEPT_READ OR ACCEPT_START *)   
    | InjR rep' ->  
      match rep' with
      (* ACCEPT *)
      | InjL () ->
        release lock; 
        Some ()
      (* ACCEPT_READ OR ACCEPT_START *)   
      | InjR _ -> assert false
 in
 let read k : 'a option =
   acquire lock;
   match active_request rpc ts (fun n -> read_req n k) with
    (* ABORT *)
    | InjL () -> assert false
    (* ACCEPT OR ACCEPT_READ OR ACCEPT_START *)   
    | InjR rep' ->  
      match rep' with
      (* ACCEPT *)
      | InjL () -> assert false
      (* ACCEPT_READ OR ACCEPT_START *)   
      | InjR rep'' ->
        match rep'' with
        (* ACCEPT_READ *) 
        | InjL vo -> 
          release lock;
          vo
        (* ACCEPT_START *)  
        | InjR _ -> assert false 
 in ((start, commit), (write, read))