open Ast
open List_code
open Queue_code
open Map_code
open Network_util_code
open Vr_serialization_code
open Vr_network_code
open! Vr_debug


let emit lk (outQ : 'a msgOutTy queue Atomic.t) (event : 'a msgTy) =
  acquire lk; outQ := queue_add (InjL event) !outQ; release lk

let emit_rpl lk (outQ : 'a msgOutTy queue Atomic.t) (event : 'a replyTy) =
  acquire lk; outQ := queue_add (InjR event) !outQ; release lk

type 'a client_tableTy = (saddr, int * 'a option option) amap Atomic.t
type 'a databaseTy = ((string, 'a) amap) Atomic.t
type pok_tableTy = (int, int Atomic.t * (bool Atomic.t alist)) amap Atomic.t
type 'a logTy = 'a requestTy alist
type svcDataTy = int Atomic.t * (bool Atomic.t alist)
type 'a dvcVoteDataTy = ((('a requestTy alist * int) * int) * int)
type 'a dvcDataTy = int Atomic.t * (('a dvcVoteDataTy option Atomic.t) alist)

(** ------------------------------------------------------------------------- *)
(** -------------- NORMAL CASE PROCESSING OF CLIENT REQUESTS ---------------- *)
(** ------------------------------------------------------------------------- *)

(* Auxiliary function to commit a request *)
(* Assumes req = log(cmtN + 1) *)
(* Assumes req.c is in the client table ctbl *)
let commit_op
    (cmtN : int Atomic.t)
    (ctable : 'a client_tableTy)
    (db : 'a databaseTy)
    (req : 'a requestTy) =
  let ((op, c), s) = req in
  let ctbl = !ctable in
  (* Process the request *)
  let res =
    match op with
    | InjL p ->                   (* write value v to the key k *)
      let (k, v) = p in
      db := map_insert k v !db;
      Some v
    | InjR k ->
      map_lookup k !db            (* read the key k *)
  in
  cmtN := !cmtN + 1;
  (* Update the client table ctbl only if the sequence id s
     is the most recent one for the client address c. *)
  let ctbl' =
    match map_lookup c ctbl with
      None -> assert false        (* commit only for existing entries. *)
    | Some p ->
      if (fst p) <= s
      then map_insert c (s, Some res) ctbl
      else ctbl
  in
  ctable := ctbl';
  ((res, c), s)

(* Assumes oplist = log[cmtN+1 .. kj] *)
let commit_oplist_at_primary cmtN ctable db oplist vi lk outQ =
  let rec aux l =
    (* Printf.printf "commit_oplist_at_primary\n%!"; *)
    match l with
    | None -> ()
    | Some p ->
      let (op, tl) = p in
      let cmtop = commit_op cmtN ctable db op in
      let ((r, c), s) = cmtop in
      emit_rpl lk outQ (rpl vi s r c);
      aux tl
  in
  aux oplist

(* Assumes oplist = log[cmtN+1 .. kj] *)
(* Since backup does not talk to clients,
   it does not emit events upon commit *)
let commit_oplist_at_backup cmtN ctable db oplist =
  let rec aux l =
    (* Printf.printf "commit_oplist_at_primary (len:%d)\n%!" (list_length oplist); *)
    match l with
    | None -> ()
    | Some p ->
      let (op, tl) = p in
      ignore(commit_op cmtN ctable db op);
      aux tl
  in aux oplist

(* TODO: explain the code. *)
let add_ptable_entry len ptable orig ni =
  (* Create a new row in a prepareOK table for the (ni+1)-th request. *)
  let okl = list_init len (fun _i -> ref false) in
  (* The primary itself counts as one prepareOK. *)
  let oki = unSOME (list_nth okl orig) in
  oki := true;
  ptable := map_insert ni (ref 1, okl) !ptable

(** Udpate ctable with all pending requests in the log_suf.
    Called only by backups of a given active view. *)
let ctbl_add_pending log_suf ctable =
  let rec aux l =
    match l with
      None -> ()
    | Some p ->
      let (req, tl) = p in
      let ((_op, c), s) = req in
      ctable := map_insert c (s, None) !ctable;
      aux tl
  in aux log_suf

(* TODO: check and explain the code. *)
(** Update ctable with all pending requests in the log_suf and prepare_ok table.
    Called by the new primary of a given active view. *)
let ctbl_ptbl_add_pending len i log_suf ctable ptable n =
  let rec aux l nj =
    match l with
      None  -> ()
    | Some p ->
      let (req, tl) = p in
      let ((_op, c), s) = req in
      (* Update client table. *)
      ctable := map_insert c (s, None) !ctable;
      add_ptable_entry len ptable i nj;
      aux tl (nj + 1)
  in aux log_suf n

let ctbl_remove_pending
    (log_suf : 'a requestTy alist) (ctable : 'a client_tableTy) =
  let ctbl = !ctable in
  let rec aux l =
    match l with
      None -> ()
    | Some p ->
      let (req, tl) = p in
      let ((_op, cl_saddr), _seqid) = req in
      match map_lookup cl_saddr ctbl with
        None -> ()
      | Some q ->
        let (_sa, resp_opt) = q in
        (* remove only pending requests *)
        match resp_opt with
        | None -> ctable := map_remove cl_saddr ctbl
        | Some _p -> ();
          aux tl
  in aux log_suf


let reinit_view_change_data (vc_data : svcDataTy) (dvc_data : 'a dvcDataTy) =
  let (vcpt, vl) = vc_data in
  let (qcpt, ql) = dvc_data in
  list_iter (fun p -> p := false) vl;
  vcpt := 0;
  list_iter (fun p -> p := None) ql;
  qcpt := 0

(** Auxiliary procedure for a backup to join a more recent active view
    upon receival of a prepare or commit message. *)
(* Implements what is described in 5.2 of VR12 paper. *)
(* Assumes (~ newView mod |l| = i) &&  ((st = false) || (viewC < newView)) *)
let join_view
    lk i len viewC viewA status cmtN opN
    ptable ctable vc_data dvc_data
    log outQ newView =
  unsafe (print_step_state i "joining view" !viewC !status (!viewC mod len) !opN !cmtN !log);
  let ki = !cmtN in
  (* Here, pAtomic.tix pAtomic.t is the committed part, and suffix suf is the pending part of the log.*)
  let lg = list_split (ki + 1) !log in
  let (pref, suf) = lg in              (* pAtomic.t, suf = lg[0..ki], lg[ki+1..|lg|] *)
  (* Since the log may contain stale pending requests, the node i
     must remove stale data, keeping only a durable pAtomic.tix of its log. *)
  opN := ki;                           (* Set op-number to commit-number.*)
  log := pref;                         (* Remove all log entries after commit-number.*)
  ctbl_remove_pending suf ctable;      (* Keep only processed entires in the ctable *)
  reinit_view_change_data vc_data dvc_data;    (* Clear the view change data. *)
  ptable := map_empty ();              (* Clear the pending commit table. *)
  (* Udpate views and status. *)
  viewC := newView;                    (* Set the current view to the new view *)
  viewA := newView;                    (* Set the last active view to the new view *)
  status := true;                      (* Set status to active *)
  (* Emit the get state event. *)
  emit lk outQ (gst newView ki i);      (* Make a request for a new state. *)
  unsafe (print_step_state i "joined view" !viewC !status (!viewC mod len) !opN !cmtN !log)



(** Processing ⟨PREPARE vj, req, nj, kj⟩ message. *)
let step_prp
    len i lk status viewC viewA opN cmtN
    log ptable ctable vc_data dvc_data db outQ prp =
  let vi = !viewC in
  let st = !status in
  let ni = !opN in
  let ki = !cmtN in
  let (((vj, req), nj), kj) = prp in
  let vJ = vj mod len in  (* The group id of the primary who is the sender of prp. *)
  if vi <= vj  (* Process the msg only if the msg view is at least as recent as
                  the current view of the node i. *)
  then
    begin
      unsafe (print_step_state i "prp" vi st (vi mod len) ni ki !log);
      (* The msg source must consider the replica i as backup of the view vj. *)
      assert (not (vJ = i));
      (* If the replica's view is stale w.r.t. the msg view vj, or if the replica i
         didn't joined yet the current view, *)
      if (st = false || vi < vj)
      (* then the replica i needs to join the view vj and to set its local state
         up to date, by asking vJ node to make a state transfer. *)
      then join_view lk i len viewC viewA status cmtN opN
          ptable ctable vc_data dvc_data log outQ vj
      else
      if nj <= ni (* Otherwise, "vi = vj" && "st = true, so consider the request nj". *)
      then ()   (* If the req's been seen, then the msg's a dupl. so ignore it. *)
      else      (* Otherwise, two cases are possible. *)
      if nj = ni + 1  (* Either only the most recent request haven't been seen by replica i, *)
      then            (* in which case process the request and send back prepareOK msg. *)
        begin
          opN := ni + 1;
          log := list_append !log (list_cons req list_nil);
          let ((_op, caddr), seqid) = req in
          ctable := map_insert caddr (seqid, None) !ctable;
          (* It is important to send confirmation before processing the requests,
             since the confirmation concerns storing the request in the log. *)
          emit lk outQ (pok vi (ni + 1) i);            (* Send confirmation to the primary. *)
          let infl = list_inf (ki + 1) kj !log in      (* Take the infix log[ki+1..kj] *)
          commit_oplist_at_backup cmtN ctable db infl  (* and process the requests inside. *)
        end
      else          (* Or, some requests are missing locally (due to message drop),
                       so the state transfert is needed. *)
        emit lk outQ (gst vj ni i)
    end
  else ()

(** Processing  ⟨COMMIT vj, kj⟩ message. *)
let step_cmt
    len i lk status viewC viewA opN cmtN
    log ptable ctable vc_data dvc_data db outQ cmt =
  let vi = !viewC in
  let st = !status in
  let ni = !opN in
  let ki = !cmtN in
  let (vj, kj) = cmt in
  let vJ = vj mod len in
  if vi <= vj then
    begin
      (* The msg source must consider the replica i as backup of the view vj. *)
      assert (not (vJ = i));
      if (st = false || vi < vj) (* Check whether replica i must join the view vj. *)
      then
        begin
          unsafe (print_step_state i "cmt" vi st (vi mod len) ni ki !log);
          join_view
            lk i len viewC viewA status cmtN opN
            ptable ctable vc_data dvc_data log outQ vj
        end
      else
      if kj <= ni (* If the commit-num of cmt is within what the replica i has seen, *)
      then        (* then commit the infix log[ki..kj] of the log. *)
        begin
          let infl = list_inf (ki + 1) kj !log in
          unsafe (fun () ->
              if not (list_is_empty infl)
              then print_step_state i "cmt" vi st (vi mod len) ni ki !log ());
          commit_oplist_at_backup cmtN ctable db infl
        end
      else                           (* Otherwise, the replica i is behind the primary, *)
        begin
          unsafe (print_step_state i "cmt" vi st (vi mod len) ni ki !log);
          emit lk outQ (gst vj ni i)   (* so it must ask it for the missing log entries.  *)
        end
        end
  else ()

(* Upon receival of prepareOK event ((vi, nj), j), process all requests
   in the log infix 'infl' = log[ cmtN+1 .. nj ]. *)
(* Assumes
      ptable(nj)(j) = false
   && vj = vi
   && cmtN < nj < |log| = opN - 1 *)
let process_prepareok_from_j
    cmtN ctable ptable db lk outQ pok log len =
  (* Printf.printf "process_prepareok_from_j\n%!"; *)
  (* loop invariant cmtN_i <= cmtN = k <= nj < |log| *)
  (* l = log[k .. nj] *)
  let ((vi, nj), j) = pok in
  let rec aux l k =
    match l with
    | None -> () (* nj <= k *)
    | Some p ->  (* We know that k < nj < |log|
                    so the entries ptable(k+1) and log(k+1) are defined. *)
      let (req, tl) = p in
      let ks = k + 1 in
      (* Check the boolean ptable(k+1)(j), i.e. whether already received a
         confirmation for k+1-th request from the backup j. *)
      let p = unSOME (map_lookup ks !ptable) in
      let (cpt, okl) = p in
      let okj = unSOME (list_nth okl j) in
      (* if yes, then the prepareOK from node j has been already counted. *)
      if !okj then aux tl ks
      else                        (* If no, then check if  the count for        *)
      if !cpt + 1 <= len / 2      (* k+1-th req + conf from j give a majority.  *)
      then                        (* If yes, then update the prepare-ok table   *)
        begin                     (* and increment the count for the k-th rqst. *)
          okj := true;
          cpt := !cpt + 1;
          aux tl ks
        end
      else   (* Otherwise, commit the request, clean ctable, and emit an event. *)
        begin
          (* let ((op, c), _s) = req (\* req = log[cmt + 1 + k] *\) in *)
          let r = commit_op cmtN ctable db req in
          let ((resp, cl_addr), seqid) = r in
          ptable := map_remove ks !ptable;
          emit_rpl lk outQ (rpl vi seqid resp cl_addr);
          aux tl ks
        end
  in
  let ks = !cmtN + 1 in
  let infl = list_inf ks nj !log  (* log[ cmtN+1 .. nj] *) in
  aux infl !cmtN


(** Processing ⟨PREPAREOK vj, nj, j⟩ message. *)
let step_pok
    len i lk status viewC opN
    cmtN log ptable ctable db outQ pok =
  let vi = !viewC in
  let st = !status in
  let ni = !opN in
  let ki = !cmtN in
  let ((vj, nj), j) = pok in
  let vJ = vj mod len in
  if vi = vj
  then
    begin
      (* the following situations are absurd
         - "vJ ≠ i" the msg source considers the replica as backup,
           but prepareOK are sent only to primary nodes
         - "st = false if the vJ = i ∧ vi = vj and st = false", then the
           node i is still waiting to become a primary of the vJ,
           but prepareOK can only be sent by a backup which has been
           in a normal mode for a view vj, which in turn is only possible
           if there was an activing the primary for the view vj.
         - "ni < nj if vJ = i ∧ st = true ∧ vj <= vi", it is not possible
           that the we receive a prepareok for a request we didn't broadcast yet.
           So we know that the following assert holds (to move to precondition ?) *)
      assert ((vJ = i) && (st = true) && (nj <= ni));
      if ki < nj
      then
        begin
          unsafe (print_step_state i "pok" vi st (vi mod len) ni ki !log);
          (* we know that ptbl(r) = (pr, lr) is defined for r ∈ [ ki+1 .. ni ] and
             each lr(t) = br is defined for t ∈ [ 0 .. len [  ∧ !pr <= ⌊len/2⌋. *)
          let p = unSOME (map_lookup nj !ptable) in
          let okj = unSOME (list_nth (snd p) j) in
          (* if node i has already seen prepareok from the node j, we're done. *)
          if !okj then ()
          (* Otherwise, we need to process the prepareok. *)
          else
            (* We know that ki < nj <= ni < |log|, so log[ki+1..nj] is defined. *)
            process_prepareok_from_j
              cmtN ctable ptable db lk outQ pok log len
              (* Ignore if the req has been seen already. *)
        end
      else ()
    end
    (* The case vi < vj is absurd and the case vj < vi can be ignored. *)
  else ()

(* Assumes vi mod len = i ∧ that request has not been seen. *)
let add_request
    len i vi ki lk opN log ptable ctable outQ req =
  (* Udpate the client table adds an first entry for a new client, or
     replace an existing entry containing an already processed request. *)
  let ((op, c), s) = req in
  let ni = !opN in
  opN  := ni + 1;
  ctable := map_insert c (s, None) !ctable;
  log  := list_append !log (list_cons ((op, c), s) list_nil);
  add_ptable_entry len ptable i (ni + 1);
  emit lk outQ (prp vi ((op, c), s) (ni + 1) ki)


(* Assumes each client can only have one outstanding request. *)
(** Processing ⟨REQUEST op, c, s⟩ event. *)
let step_req
    len i lk status viewC opN
    cmtN log ptable ctable outQ (req : 'a requestTy) =
  let vi = !viewC in
  let ki = !cmtN in
  (* let ni = !opN in *)
  let vI = vi mod len in
  (* Only the primary of the view vi shall process client requests *)
  if (vI = i) && (!status = true) then (* replica i is an active primary *)
    let ((_op, c), s) = req in
    (* Check whether the request has been already processed. *)
    match map_lookup c !ctable with
      None -> (* New client *)
      unsafe (print_step_state i "req" vi !status (vi mod len) !opN ki !log);
      add_request len i vi ki lk opN log ptable ctable outQ req
    | Some p ->
      let (t, ro) = p in
      if s < t then () (* Ignore stale requests. *)
      else
        match ro with
        (* When the request is pending,
           - either s = t, and then the request can be ignored,
           - or t < s, which is only possible if the node i is not the most
             recent primary (that follows from the fact that each client can
             have only one outstanding request). In this case we can choose
             simply ingore the request, waiting for a msg from a more recent
             primary. Other choices are possible, e.g. find out who's the
             primary and ask for a state transfer, or allow state transfer
             between backups. *)
          None -> ()
        (* Here we know that the last client's request has been processed. *)
        | Some res ->
          unsafe (print_step_state i "req" vi !status (vi mod len) !opN ki !log);
          (* If the same request, just resend the acknowledgement *)
          if s = t then emit_rpl lk outQ (rpl vi s res c)
          else (* Otherwise t < s, i.e. node i hasn't yet seen the request,
                  so add the request (overwrites client's previous request. *)
            add_request len i vi ki lk opN log ptable ctable outQ req
            (* Ohterwise, the node i is a backup of the veiw vi, so ignore the request *)
            (* TODO think about retransmitting the request to the primary ? *)
  else ()

(** ------------------------------------------------------------------------- *)
(** ------------------------- VIEW CHANGE PROTOCOL -------------------------- *)
(** ------------------------------------------------------------------------- *)


(* Choosing the best dvc data following 4.2.3 paragraph from the paper. *)
let rec find_best_dvc
      (best : 'a dvcVoteDataTy option)
      (l : 'a dvcVoteDataTy option Atomic.t alist)
      (flag : bool) =
    match l with
    | None -> best
    | Some p ->
      let (x, tl) = p in
      match !x with
      | None -> find_best_dvc best tl flag (* Continue, since no dvc data from that replica. *)
      | Some qev ->                        (* Find if the dvc data from that replica is the best. *)
        if flag
        then begin
          let b = unSOME best in
          let (((_bl, bv), bn), _bk) = b in
          let (((_ql, qv), qn), _qk) = qev in
          if qv < bv
          then find_best_dvc best tl flag       (* Keep best, if best has a more recent view. *)
          else if bv < qv                       (* If that replica has more recent view, *)
          then find_best_dvc (Some qev) tl flag (* then set the best to that replica's dvc data. *)
          else if qn <= bn                      (* In cas of same view, take the best op-number *)
          then find_best_dvc best tl flag
          else find_best_dvc (Some qev) tl flag
        end
        else
          find_best_dvc (Some qev) tl true

(** Auxiliary function for a replica to start acting
    as a primary of the new view. *)
(* Assumes that dvc_data has a quorum of dvc data, i.e.at least |len|/2 + 1
   elements of dvc_data are equal to some qev. *)
(* Assumes that ptable is empty *)
let view_change_success
    len i lk status viewC viewA opN cmtN
    log ctable ptable
    vc_data dvc_data
    db outQ =
  unsafe (print_step_state i "install nv" !viewC !status (!viewC mod len) !opN !cmtN !log);
  ignore (assert (!viewC mod len = i));               (* Replica can be the primary *)
  let (_cpt, vl) = dvc_data in
  let newData = find_best_dvc None vl false in        (* Find the best dvc data. *)
  let b = unSOME newData in
  let (((lb, vb), nb), kb) = b in
  let ki = !cmtN in
  let vi = !viewC in
  let li = !log in
  let k_max = if ki <= kb then kb else ki in
  let split_li =  list_split (k_max + 1) li in
  let split_lb =  list_split (k_max + 1) lb in
  let (lip, lis) = split_li in   (* li[0..k_max], li[k_max+1..|li|] *)
  let (lbp, lbs) = split_lb in   (* lb[0..k_max], lb[k_max+1..|lb|] *)
  (* One of the key properties of the protocol is that both the new and old logs
     have the same durable pAtomic.tix. TheAtomic.tore, it must hold in the program that up
     to the commit-num m = max(ki,kj) the pAtomic.tixes [0..m] of li and lb are the same. *)
  assert (lip = lbp);
  assert (vb = vi);      (* The current view should be the same as the best one. *)
  (* Synchronize local data. *)
  viewA := vi;
  opN := nb;
  log := list_append lip lbs ; (* The new log is indeed set to the best bl = lip ++ lbs. *)
  status := true;
  reinit_view_change_data vc_data dvc_data;
  (* Update the client table ctable. *)
  (* As the ctable contain the data associated with the suffix li[k_max+1 |li|] of the
     old log li, the ctable may contain pending requests some of which potentially aren't
     coming from a quorum, so the ctable must be updated, by removing the suffix
     li[k_max..|li|] and adding lb[k_max..|lb|] requests instead. *)
  ctbl_remove_pending lis ctable;
  ctbl_ptbl_add_pending len i lbs ctable ptable (k_max + 1);
  (* Inform the replicas that a new view has succeeded. *)
  emit lk outQ (snv vi lb nb !cmtN);
  (* Finally, re-commit the new log entries log[ki+1..kb]. *)
  let infl = list_inf ki kb !log in
  commit_oplist_at_primary cmtN ctable db infl vi lk outQ;
  unsafe (print_step_state i "nv installed" !viewC !status (!viewC mod len) !opN !cmtN !log)


(** Add a dvc (log, etc.) to the dvc_data from the replica orig. *)
let add_dvc
    len i lk status viewC viewA opN cmtN
    log ctable ptable svc_data (dvc_data : 'a dvcDataTy) db outQ
    dvc orig svc_flag =
  let (qcpt, ql) = dvc_data in
  let tmp = !qcpt in
  let qtj = unSOME (list_nth ql orig) in
  match !qtj with
  | Some _q -> ()
  | None ->
    qcpt := tmp + 1;
    qtj  := Some dvc;
    if tmp + 1 <= len / 2
    then
      if svc_flag then emit lk outQ (svc !viewC i) else ()
    else
      view_change_success
        len i lk status viewC viewA opN cmtN
        log ctable ptable svc_data dvc_data db outQ

(** Add a svc (vote) to the svc_data from the replica orig. *)
let add_svc len i lk vi va ni ki lg outQ svc_data orig svc_flag =
  let (vcpt, vl) = svc_data in
  let tmp = !vcpt in
  if len / 2 < tmp then ()  (* If there is already a quorum of votes, message can be ignored. *)
  else                      (* Otherwise, if not already, the vote orig must be taken into account. *)
    let voteJ = unSOME (list_nth vl orig) in
    if !voteJ then () (* The vote of orig has been already recorded, so nothing to do. *)
    else              (* Otherwise, record the vote of orig and increment the votes count. *)
      begin
        voteJ := true;
        vcpt  := tmp + 1;
        if tmp + 1 <= len / 2                                        (* The quorum is not reached *)
        then if svc_flag then emit lk outQ (svc vi i) else ()        (* Emit svc if not yet done. *)
        else emit lk outQ (dvc vi lg va ni ki i)                     (* Emit dvc for the fst time. *)
      end

(** Initiate the view change protocol when
    the newView mod len matches the replica's own id. *)
(* Assumes that the status is false, svc_data is empty.  *)
let view_change_init_primary
    len lk i
    viewC viewA opN cmtN status log
    ctable ptable svc_data dvc_data db
    outQ newView trigger_event =
  (* First, add the replica's own dvc data. *)
  add_dvc
    len i lk status viewC viewA opN cmtN
    log ctable ptable svc_data (dvc_data : 'a dvcDataTy) db outQ
    (((!log, newView), !opN), !cmtN) i true;
  (* Then process what has triggered the view change. *)
  match trigger_event with
  | None -> ()                          (* Initiated because of timeout. *)
  | Some ev ->
    match ev with
    | InjL _orig -> ()                  (* Initiated because of svc event. *)
    | InjR dvc_ev ->                       (* Initiated because of dvc event. *)
      let (dvcj, j) = dvc_ev in
      add_dvc
        len i lk status viewC viewA opN cmtN
        log ctable ptable svc_data (dvc_data : 'a dvcDataTy) db outQ
        dvcj j false

(** Initiate the view change protocol when
    the newView mod len does not match the replica's own id. *)
(* Assumes that the status is false, svc_data is empty.  *)
let view_change_init_backup
    len lk i vi va ni ki lg svc_data outQ newView trigger_event =
  match trigger_event with
  | None ->                                        (* Initiated because of timeout. *)
    add_svc len i lk vi va ni ki lg outQ svc_data i true;
    emit lk outQ (svc newView i)
  | Some j ->                                      (* Initiated because of svc event. *)
    add_svc                                        (* Add a vote for the orig of svc event. *)
      len i lk vi va ni ki lg outQ svc_data j true

(** Initiate the view change protocol. *)
let view_change_init
    len lk i
    viewC viewA opN cmtN status log
    ctable ptable svc_data dvc_data db
    outQ newView trigger_event =
  status := false;                                       (* Leave active mode. *)
  reinit_view_change_data svc_data dvc_data;             (* Reinitialize tables and lists. *)
  ptable := map_empty ();                                (* Clear prepare-ok table. *)
  viewC  := newView;                                     (* The viewA is left behind now. *)
  unsafe (print_step_state_vc i "vc init" !viewC !status (!viewC mod len) !opN !cmtN !log 0 0);
  let vI = newView mod len in
  if vI = i           (* Depending on whether on the future role of the replica i *)
  then                (* in the newView, initiate the VC protocol as primary or as backup. *)
    view_change_init_primary
      len lk i viewC viewA opN cmtN status log
      ctable ptable svc_data dvc_data db outQ newView trigger_event
  else
    let trigger_event =
      match trigger_event with
      | None -> None                                     (* Initiated because of timeout. *)
      | Some ev ->
        match ev with
        | InjL orig -> Some orig                         (* Initiated because of svc event.  *)
        | InjR _dvc -> assert false                      (* As the replica will be backup in *)
    in                                                   (* the newWiew, it cannot be the case *)
    view_change_init_backup                              (* that it has received a dvc event. *)
      len lk i !viewC !viewA !opN !cmtN !log svc_data outQ newView trigger_event


(** ⟨STARTVIEWCHANGE vj, j⟩ *)
let step_svc
    len i lk
    status viewC viewA opN cmtN
    log ctable ptable svc_data dvc_data db
    outQ svc =
  let vi = !viewC in
  let st = !status in
  let (vj, j) = svc in
  let vI = vi mod len in
  if vi < vj then        (* If there is a higher view, join it. *)
    begin
      unsafe (print_step_state i "svc" vi st (vi mod len) !opN !cmtN !log);
      view_change_init len lk i viewC viewA opN cmtN status log
        ctable ptable svc_data dvc_data db outQ vj (Some (InjL j))
    end
  else
  if (vj < vi || st)     (* If the view vj is stale or if it has been already activated, *)
  then ()                (* then the svc event is not relevant any more, so ignore it. *)
  else                   (* Otherwise, we know that vi = vj and st = false. *)
  if vI = i              (* If the replica i will be the primary of its view, *)
  then ()                (* Then, nothing to do (and because st = false, emit svc already happened). *)
  else                   (* Otherwise, the node will be the backup of its view, so process the vote j.*)
    add_svc len i lk !viewC !viewA !opN !cmtN !log outQ svc_data j false

(** ⟨DOVIEWCHANGE vj, lj, vj’, nj, kj, j⟩ *)
let step_dvc
    len i lk
    viewC viewA opN cmtN status log
    ctable ptable svc_data dvc_data db outQ (dvc : 'a dvcTy) =
  let vi = !viewC in
  let st = !status in
  let (((((vj, lj), vaj), nj), kj), j) = dvc in
  let vI =  vi mod len in
  let vJ =  vj mod len in
  if vi < vj                      (* If there is a higher view, join it. *)
  then
    begin
      unsafe (print_step_state i "dvc" vi st (vi mod len) !opN !cmtN !log);
      view_change_init len lk i viewC viewA opN cmtN status log
        ctable ptable svc_data dvc_data db outQ vj (Some (InjR ((((lj, vaj), nj), kj), j)))
    end
  else
  if (vj < vi || st)     (* If the view vj is stale or if it has been already activated, *)
  then ()                (* then the dvc event is not relevant any more, so ignore it. *)
  else                   (* Otherwise, we know that vi = vj and st = false. *)
    begin                (* We also know that the node'll be the primary of the new view. *)
      unsafe (print_step_state i "dvc" vi st (vi mod len) !opN !cmtN !log);
      assert (vJ = i && vI = vJ);
      add_dvc
        len i lk status viewC viewA opN cmtN
        log ctable ptable svc_data dvc_data db outQ
        (((lj, vaj), nj), kj) j false
    end



(* TODO: check and explain more the code. *)
(** ⟨STARTVIEW vj, lj, nj, kj⟩ *)
let step_snv
    len i lk
    viewC viewA opN cmtN status
    log ctable ptable svc_data dvc_data db outQ snv =
  let vi = !viewC in
  let st = !status in
  let ki = !cmtN in
  let li = !log in
  let (((vj, lj), nj), kj) = snv in
  let vJ = vj mod len in
  if (((vi = vj) && (not st)) || vi < vj)
  then
    begin
      unsafe (print_step_state i "snv start" vi st (vi mod len) !opN !cmtN !log);
      assert (not (vJ = i));
      let k_max = if ki <= kj then kj else ki in
      let split_li =  list_split (k_max + 1) li in
      let split_lj =  list_split (k_max + 1) lj in
      let (lip, lis) = split_li in
      let (ljp, ljs) = split_lj in
      (* One of the key properties of the protocol is that both the new and old logs
         have the same durable pAtomic.tix. TheAtomic.tore, it must hold in the program that up
         to the commit-num m = max(ki,kj) the pAtomic.tixes [0..m] of li and lb are the same. *)
      assert (lip = ljp);
      (* Synchronize local data. *)
      viewC := vj;
      viewA := vj;
      opN := nj;
      log := list_append lip ljs ; (* lip ++ ljs = kj *)
      status := true;
      (* Reinitialize tables and lists. *)
      ptable := map_empty ();
      reinit_view_change_data svc_data dvc_data;
      (* The suffix li[k_max ..] the ctbl should contain only pending entires some
         of which potentially aren't coming from a quorum, so the ctbl
         must be updated, by removing li[mx..] and adding lj[mx..] requests. *)
      ctbl_remove_pending lis ctable;
      ctbl_add_pending ljs ctable;
      (* If needed, send prepareok to the new primary. *)
      (if nj < kj then emit lk outQ (pok vj nj i) else ());
      (* Finally, commit locally data that have not yet been commited.
         If kj < ki = mx = !cmtN, then there is nothing to commit and
         no need to update the cmtN number. Otherwise, !cmtN = ki <= kj = mx,
         so if ki < kj, then commit requests from log[ki + 1 .. mx] *)
      let infl = list_inf ki kj !log in
      commit_oplist_at_backup cmtN ctable db infl;
      (* Otherwise, vj < vi or (vj = vi && st = true), so ignore. *)
      unsafe (print_step_state i "snv done" vi st (vi mod len) !opN !cmtN !log);
    end
  else ()


(** ------------------------------------------------------------------------- *)
(** ---------------------- STATE TRANSFER PROCESSING ------------------------ *)
(** ------------------------------------------------------------------------- *)

(* TODO: check and explain more the code. *)
(** ⟨GETSTATE vj, nj, j⟩ *)
let step_gst
    len i lk viewC opN cmtN status log outQ gst =
  let vi = !viewC in
  let st = !status in
  let ni = !opN in
  let ki = !cmtN in
  let ((vj, nj), j) = gst in
  let vJ = vj mod len in
  if vi = vj
  then
    begin
      unsafe (print_step_state i "gst" vi st (vi mod len) !opN !cmtN !log);
      assert ((vJ = i) && (st = true) && (nj <= ni)); (* Subtle! *)
      if nj < ni
      then     (* Send reply if there're ops that the node j haven't seen yet. *)
        let lsuf = list_suf (nj + 1) !log in
        emit lk outQ (nst vi lsuf ni ki j)
      else () (* Otherwise, the primary has no ops that j didn't see already. *)
      (* - The case vi < vj is absurd because we restrict gst msgs to be send only
         by backups of the view vj in response to a primary's prp or cmt message
         with the view vj s.t. either vj = vi = viA or vj > viA, in which case
         vi and viA are first set to vj before sending gst msg.
         - The case the case vj < vi can be ignored. *)
    end
  else ()

(* TODO: check and explain more the code. *)
(** ⟨NEWSTATE vj, lj, nj, kj⟩ *)
let step_nst
    len i lk viewC opN cmtN status
    log ctable db outQ nst =
  let vi = !viewC in
  let st = !status in
  let ni = !opN in
  let ki = !cmtN in
  let ((((vj, lj), nj), kj), _j) = nst in
  let vJ =  vj mod len in
  if vi = vj
  then
    begin
      unsafe (print_step_state i "nst" vi st (vi mod len) !opN !cmtN !log);
      assert ((not (vJ = i)) && (st = true));
      if ni < nj
      then
        let lnew = list_inf ni nj lj in
        log :=  list_append !log lnew;
        opN := nj;
        (* First, add new entries to the ctbl. *)
        ctbl_add_pending lnew ctable;
        (* send pok only for the last entry, as the primary will process all
           previous entries between ni..nj if needed. *)
        emit lk outQ (pok vi nj i);
        (* Finally, commit entries between [ki+1..kj] if ki < kj *)
        let infl = list_inf ki kj !log in
        commit_oplist_at_backup cmtN ctable db infl
        (* Otherwise, between sending gst & receiving nst, the node i
           has received enough prp msgs so that nst can be ignored now. *)
      else ()
    end
    (* The case vi < vj is absurd and the case vj < vi can be ignored. *)
  else ()



(** ------------------------------------------------------------------------- *)
(** ------------------------------- EVENT LOOP ------------------------------ *)
(** ------------------------------------------------------------------------- *)

let queue_length q =
  list_length (fst q) + list_length (snd q)


(** Fetch from network the head of the queue, if any, and the value
    of the monitor of the replica's view.
    The i*)
let fetch_from_network
    _i lk (monitors : bool Atomic.t alist) (inQ : 'a queue Atomic.t) vi len =
  let vI = vi mod len in
  let ev_opt =
    if not (queue_is_empty !inQ)
    then
      begin
        acquire lk;
        let tmp = !inQ in
        if not (queue_is_empty tmp)
        then
          begin
            let q = unSOME (queue_take_opt tmp) in
            let (hd, tl) = q in
            ignore(inQ := tl);
            release lk;
            Some hd
          end
        else None
      end
    else None
  in
  let mon = !(unSOME (list_nth monitors vI)) in
  (ev_opt, mon)

(** Event loop on the replica i. *)
let event_loop
     len i
    status viewC viewA opN cmtN log
    ctable ptable vc_data dvc_data
    db lk inQ outQ monitors shl =
  let rec loop () : unit =
    let vi = !viewC in
    let vI = vi mod len in
    (* Fetch the next event (if any) and the monitor of the current view's primary. *)
    let ffn = fetch_from_network i lk monitors inQ vi len in
    let (ev_opt, mon) = ffn in
    (* Check the monitor to either stay in the view or initiate a view change. *)
    begin
      if mon then ()      (* If the current view's primary is talking, then do nothing.  *)
      else                (* Otherwise, the current view's primary seems unresponsive. *)
      if (vI = i)         (* In that case, if the replica is the primary of its view, then the *)
      then                (* monitor being false means that there are no new incoming requests. *)
        if !status        (* In that case, if the primary is active, *)
        then              (* then it sends a ping to all backups in form of a commit message. *)
          emit lk outQ (cmt vi !cmtN)
        else ()           (* Otherwise, the replica is not yet an active primary, so do nothing. *)
      else                (* Finally, if the replica isn't the primary of its view, then since *)
        begin             (* the view's primary seems unresponsive, initiate the view change. *)
          let vI_next = (vi + 1) mod len in
          let sh_old = unSOME (list_nth shl vI) in
          let sh_new = unSOME (list_nth shl vI_next) in
          setReceiveTimeout sh_old 3 0;
          setReceiveTimeout sh_new 15 0;
          unsafe (fun () -> Printf.eprintf "Noticed timeout! Changing views: %d to %d %!\n" vi (vi+1));
          view_change_init
          len lk i
          viewC viewA opN cmtN status log
          ctable ptable vc_data dvc_data db
          outQ (vi + 1) None
        end
    end;
    unsafe ( fun () ->
      let vcpt = fst vc_data in
      let dcpt = fst dvc_data in
      if !status = false
      then
        print_step_state_vc i "event step" !viewC !status (!viewC mod len) !opN !cmtN !log !vcpt !dcpt ());
    (* Process the next event if any. *)
    match ev_opt with
      None ->
      unsafe (fun () -> Unix.sleepf 0.5);
      loop ()
    | Some event ->
      begin
        match event with
        | InjL l___ ->
          begin
            match l___ with
            | InjL ll__ ->
              begin
                match ll__ with
                | InjL lll_ ->
                  begin match lll_ with
                    | InjL llll ->
                      (* Printf.printf "VR[%d] process PRP event\n%!" i; *)
                      step_prp len i lk status viewC viewA opN cmtN
                        log ptable ctable vc_data dvc_data db outQ llll
                    | InjR lllr ->
                      (* Printf.printf "VR[%d] process CMT event\n%!" i; *)
                      step_cmt len i lk status viewC viewA opN cmtN
                        log ptable ctable vc_data dvc_data  db outQ lllr
                  end
                | InjR llr_ ->
                  begin
                    match llr_ with
                    | InjL llrl ->
                      step_pok len i lk status viewC opN
                        cmtN log ptable ctable db outQ llrl
                    | InjR llrr ->
                      step_svc len i lk status viewC viewA opN cmtN
                        log ctable ptable vc_data dvc_data db outQ llrr
                  end
              end
            | InjR lr__ ->
              begin
                match lr__ with
                | InjL lrl_ ->
                  begin
                    match lrl_ with
                    | InjL lrll ->
                      step_dvc len i lk
                        viewC viewA opN cmtN status
                        log ctable ptable vc_data dvc_data db outQ lrll
                    | InjR lrlr ->
                      step_snv len i lk
                        viewC viewA opN cmtN status
                        log ctable ptable vc_data dvc_data db outQ lrlr
                  end
                | InjR rr_ ->
                  begin
                    match rr_ with
                    | InjL lrrl ->
                      step_gst len i lk viewC opN cmtN status log outQ lrrl
                    | InjR lrrr ->
                      step_nst len i lk  viewC opN cmtN status log ctable db outQ lrrr
                  end
              end
          end
        | InjR r___  ->
          step_req
            len i lk status viewC opN
            cmtN log ptable ctable outQ r___
      end;
      loop ()
  in loop ()


(** ------------------------------------------------------------------------- *)
(** ----------------------- INITIALISATION PROCEDURE ------------------------ *)
(** ------------------------------------------------------------------------- *)



let init
    (val_ser[@metavar])
    (cfg : saddr alist alist) (* configuration square matrix *)
    i (* the index of the replica *) =
  let cfg_i = unSOME (list_nth cfg i) in
  let len   = list_length cfg_i in
  (* ---------------- local state  for application logic ----------------- *)
  (* --- local state --- *)
  (* the view-number equal to the current primary index in config *)
  let viewC = ref 0 in (* viewA (last view where replica was active)  <= viewC (current) *)
  let viewA = ref 0 in
  (* the current status ∈ { true for normal; false for "view-change" } *)
  let status = ref true in (* status = true => viewA = viewC  <=? *)
  (* the log of received requests so far in a global order *)
  let log = ref list_nil in
  (* the most recently received request *)
  let opN = ref (-1) in
  (* the op-number of the most recently commited operation *)
  let cmtN = ref (-1) in (* index of statically known durable prefix of the log  *)
  (* the table with the most recent request info for each client *)
  (* client table : caddr -> (seqid, pending|processed reqest) *)
  let (ctable : 'a client_tableTy) = ref (map_empty ()) in
  (* prepare table: *)
  let (ptable : pok_tableTy) = ref (map_empty ()) in
  (* Two wiew change tables: start view change and do view change. *)
  let svc_data = (ref 0, list_init len (fun _j -> ref false)) in
  let (dvc_data : 'a dvcDataTy )= (ref 0, list_init len (fun _j -> ref None)) in
  (* --- a specific service the key-value store --- *)
  let db = ref (map_empty ()) in
  (* ------------- network communication layer  ------------- *)
  let netdata = init_network val_ser cfg i in
  let ((((lk, inQ), outQ), monitors), shl) = netdata in
  (* ------------- state replication layer  ------------- *)
  unsafe (print_first_line);
  event_loop
    len i
    status viewC viewA opN cmtN
    log ctable ptable svc_data dvc_data db
    lk inQ outQ monitors shl

(*

Some invariants on the local data of a replica.
===============================================


View pointers viewC and viewA
---------------------------------

viewC points to the current view of the replica.
viewA points to the last view in which the replica was active.

Between each transition step of the event loop
st=True  -> viewA = viewC
st=False -> viewA < viewC

Client table ctbl.
-------------------

ctbl caddr -> option (nat, option val)

ctbl(c) = None
-> c ∉ dom(ctbl)

ctbl(c) = Some (s, None)
-> request (c,s) is being processed

ctbl(c) = Some (s, Some None)
-> request (c,s) must be a read k request that has been processed,
   but the distributed database at the key k is undefined

ctbl(c) = Some (s, Some (Some v))
-> request (c,s) must be a write k v request or a read k that
   has been successfully processed.



Relation between client table ctbl and log, opN, and cmtN.
------------------------------------------------------------------

ctbl(c) = Some (s, ro) :=>
  ∃ n op, log(n) = Some (op, c, s)                        (CTBL-1)
  ∧ (∀ p x, n < p, log(p) = Some x -> x.c ≠ c)            (CTBL-2)
  ∧ (∀ p x, p < n, log(p) = Some x -> x.c = c -> x.s < s) (CTBL-3)
  ∧ (ro ≠ None :=> n <= cmtN)                              (CTBL-4)

The entries of the ctbl correspond exactly to the most recent
request entries of the log for the respective clients (CTBL-1,2,3).
Moreover, the request is marked as processed (ro ≠ None) in the ctbl iff
the request is stored in the durable part of the log.

That is, in the current implementation, in the following situations,
the client table is recomputed starting from the durable part of the log
- when, due to prp or cmt event, a backup is lagged behind and asks
  for a state transfer.
- when, after the election, a new primary activation its view.


TODO prepare table
------------------------------------------------------------------
*)
