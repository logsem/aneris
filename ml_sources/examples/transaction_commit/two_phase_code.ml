open Ast
open Set_code
open Map_code
open Network_util_code
open Coin_flip_code
open Nodup_code

let resource_manager rm tm =
  let skt = udp_socket () in
  socketBind skt rm;
  let msg = unSOME (receiveFrom skt) in
  let value = fst msg in
  (* someone already aborted *)
  if value = "ABORT" then sendTo skt "ABORTED" tm
  else
    (* tm proposes to commit; locally make a decision as well *)
    let local_abort = coin_flip () in
    if local_abort then sendTo skt "ABORTED" tm
    else
      begin
        (* prepared to commit *)
        ignore(sendTo skt "PREPARED" tm);
        (* wait for tms decision *)
        let msg = wait_receivefrom skt
            (fun m -> (fst m = "COMMIT") || (fst m = "ABORT")) in
        let decision = fst msg in
        if decision = "COMMIT" then
          (* all agreed to commit *)
          sendTo skt "COMMITTED" tm
        else
          (* someone aborted *)
          sendTo skt "ABORTED" tm
      end

let recv_responses recv skt rms =
  let rec loop prepared  =
    (set_equal prepared rms) ||
    let msg = recv skt in
    (fst msg = "PREPARED") &&
    (loop (set_add (snd msg) prepared)) in
  loop (set_empty ())

let transaction_manager tm rms =
  let skt = udp_socket () in
  socketBind skt tm;
  let recv = nodup_init () in
  sendto_all_set skt rms "PREPARE";
  let all_prepared = recv_responses recv skt rms in
  if all_prepared
  then
    begin
      sendto_all_set skt rms "COMMIT";
      let resps = receivefrom_nodup_set skt recv rms in
      map_iter (fun _rm m ->
          assert (m = "COMMITTED")) resps;
      "COMMITTED"
    end
  else
    begin
      ignore(sendto_all_set skt rms "ABORT");
      "ABORTED"
    end
