open! Ast
open! List_code
open! Set_code
open! Map_code
open Network_util_code
open Serialization_code
let ballot_serializer = int_serializer

(* either [prepare(b)] or [accept(b, v)] *)
let acceptor_serializer (value_serializer[@metavar]) =
  sum_serializer ballot_serializer
    (prod_serializer ballot_serializer
      value_serializer)

(* The paylod of a [promise(b, (b', v)?)] message is a ballot number and a
   possibly already accepted value and its ballot *)
let proposer_serializer (value_serializer[@metavar]) =
  prod_serializer ballot_serializer
    (option_serializer
       (prod_serializer ballot_serializer
          value_serializer))

(* The paylod of an [ack] message is the proposal number and an accepted
   value *)
let learner_serializer (value_serializer[@metavar]) =
  prod_serializer ballot_serializer value_serializer

let client_serializer (value_serializer[@metavar]) =
  prod_serializer ballot_serializer value_serializer

let acceptor (valS[@metavar]) learners addr =
  let skt = socket PF_INET SOCK_DGRAM IPPROTO_UDP in
  socketBind skt addr;
  let maxBal = ref None in
  let maxVal = ref None in
  let rec loop () =
    let msg = unSOME (receiveFrom skt) in
    let m = fst msg in
    let sender = snd msg in
    begin
      match (acceptor_serializer valS).s_deser m with
        InjL bal ->
          let b = !maxBal in
          if (b = None) || (unSOME b < bal) then
            begin
              maxBal := Some bal;
              ignore(sendTo skt ((proposer_serializer valS).s_ser ((bal, !maxVal))) sender)
            end
          else ()
      | InjR accept -> (* accept(bal, v) *)
          let bal = fst accept in
          let _v = snd accept in
          (* A proposal is accepted unless the acceptor has already respondend to
             a [prepare] request having a ballot greater than [bal] *)
          let b = !maxBal in
          if (b = None) || (unSOME b <= bal) then
            begin
              maxBal := Some bal;
              maxVal := Some accept;
              ignore(sendto_all_set skt learners ((learner_serializer valS).s_ser accept))
            end
          else ()
    end;
    loop () in
  loop ()


let recv_promises (valS[@metavar])
    skt           (* socket to receive from *)
    n             (* no of promises to receive *)
    bal          (* ballot to consider *) =
  let promises = ref (set_empty ()) in
  let senders = ref (set_empty ()) in
  let rec loop () =
     if set_cardinal !senders = n then !promises
     else
       let msg = unSOME (receiveFrom skt) in
       let promise =  (proposer_serializer valS).s_deser (fst msg) in
       let sender = snd msg in
       let bal' = fst promise in
       let mval = snd promise in
       (if (bal = bal')
        then
          begin
            senders := set_add sender !senders;
            promises := set_add mval !promises
          end
        else ();
        loop ()) in
   loop ()

let find_max_promise l =
  set_foldl
    (fun acc promise ->
       match promise with
         Some p ->
           begin
             match acc with
               Some a ->
                 let b1 = fst p in
                 let b2 = fst a in
                 if b1 < b2 then acc else promise
             | None -> promise
           end
       | None -> acc)
   None l



let proposer (valS[@metavar])
   acceptors              (* set of acceptor addresses *)
      skt                    (* socket for communication *)
      bal                    (* unique proposal number *)
      v                     (* value to possibly propose *)
  =
  (* Phase 1 *)
  (* the proposer sends a [prepare] request for proposal [n] to a majority
     acceptors (here we send to all) *)
  sendto_all_set skt acceptors ((acceptor_serializer valS).s_ser (InjL bal)) ;
(* Phase 2 *)
(* if the proposer receives a reponse [promise] to its [prepare] request for
   [bal] from a majority of acceptors, it sends an [accept] request to each of
   those acceptors for proposal [bal] with a value [w] where [w] is the value
   of the highest-numbered proposal among the responses, or [v] if the
   respones reported no proposal *)
  let majority_size = (set_cardinal acceptors / 2) + 1 in
  let promises = recv_promises valS skt majority_size bal in
  let max_promise = find_max_promise promises in
  let accept_value =
    match max_promise with
      Some p -> snd p
    | None -> v
  in
  sendto_all_set skt acceptors
    ((acceptor_serializer valS).s_ser (InjR (bal, accept_value)))


let proposer'
    (valS[@metavar])
   acceptors              (* set of acceptor addresses *)
      addr                   (* address to communicate on *)
      i                      (* unique proposer number *)
      n                      (* number of proposers *)
      v                    (* value to possibly propose *)
  =
  let skt = socket PF_INET SOCK_DGRAM IPPROTO_UDP in
  socketBind skt addr;
  let ballot_counter = ref 0 in
  let rec loop () =
    let ballot = !ballot_counter * n + i in
    (proposer valS) acceptors skt ballot v;
    ballot_counter := !ballot_counter + 1;
    loop () in
  loop ()

let learner (valS[@metavar])
    skt                    (* address for communcation *)
    acceptors            (* set of acceptor addresses *)
  =
  let majority_size = (set_cardinal acceptors / 2) + 1 in
  (* map from ballot numbers to sets of acceptors *)
  let votes_ref = ref (map_empty ()) in
  let rec loop () =
    let msg = unSOME (receiveFrom skt) in
    let vote = (learner_serializer valS).s_deser (fst msg) in
    let bal = fst vote in
    let value = snd vote in
    let sender = snd msg in
    let votes = !votes_ref in
    let bal_votes =
      match map_lookup bal votes with
        Some vs -> vs
      | None -> set_empty ()
    in
    let bal_votes' = set_add sender bal_votes in
    if set_cardinal bal_votes' = majority_size
    then (bal, value)
    else
      begin
        votes_ref := map_insert bal bal_votes' votes;
        loop ()
      end in
  loop ()

let learner' (valS[@metavar]) acceptors addr client =
  let skt = socket PF_INET SOCK_DGRAM IPPROTO_UDP in
  socketBind skt addr;
  let z = learner valS skt acceptors in
  sendTo skt ((client_serializer valS).s_ser z) client


let client (valS[@metavar]) addr =
  let skt = socket PF_INET SOCK_DGRAM IPPROTO_UDP in
  socketBind skt addr;
  let msg1 = unSOME (receiveFrom skt) in
  let sender1 = snd msg1 in
  let m1 = (client_serializer valS).s_deser (fst msg1) in
  let val1 = snd m1 in
  let msg2 = (wait_receivefrom skt (fun m -> not (snd m = sender1))) in
  (* Format.printf
     "orig of learners for msg1 and msg2: (%s, %d) and (%s, %d) \n%!"
     (ip_of_address sender1)
     (port_of_address sender1)
     (ip_of_address (snd msg2))
     (port_of_address (snd msg2)); *)
  let m2 = (client_serializer valS).s_deser (fst msg2) in
  let val2 = snd m2 in
  (* Format.printf "received values: (%d, %d) \n%!" val1 val2; *)
  assert (val1 = val2);
  val1
