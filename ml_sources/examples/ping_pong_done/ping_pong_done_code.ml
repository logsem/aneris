open Ast
open Network_util_code

let pong addr =
  let skt = udp_socket () in
  socketBind skt addr;
  (* Receiving the initial message. We check that the body is "PING". *)
  let msg = unSOME (receiveFrom skt) in
  let sender = snd msg in
  assert (fst msg = "PING");
  (* Sending "PONG" in response *)
  ignore (sendTo skt "PONG" sender);
  (* When listening to the socket, we may receive duplicates of the initial
   * "PING" message. Thus, we proceed to a loop that ignores any received
   * until we receive a message that is not "PING". *)
  let rec loop () =
    let ack = unSOME (receiveFrom skt) in
    let body = fst ack in
    (* The body of the first message that is not "PING" is returned. *)
    if body = "PING" then loop () else body
  in loop ()
  
 let ping addr server =
  let skt = udp_socket () in
  socketBind skt addr;
  (* Sending the inital "PING" message. *)
  ignore (sendTo skt "PING" server);
  (* Receiving a response. We have to check that the body of the message in "PONG". *)
  let msg = unSOME (receiveFrom skt) in
  assert (fst msg = "PONG");
  (* Closing the protocol by sending the final "DONE" message. *)
  ignore (sendTo skt "DONE" server)
