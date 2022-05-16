open! Ast
open List_code
open Network_util_code


let mk_udp_socket () = socket PF_INET SOCK_DGRAM IPPROTO_UDP

let server_aux addr j0 =
  let sckt = mk_udp_socket () in
  socketBind sckt addr;
  let rec handler j msg sender =
    let tag = unSOME (s2i (tag_of_message msg)) in
    let value = value_of_message msg in
    if j = tag then
      (ignore(sendTo sckt ((i2s tag) ^ "_" ^ value) sender);
       listen sckt (handler (j + 1)))
    else
      (ignore(sendTo sckt ((i2s tag) ^ "_" ^ value) sender);
       listen sckt (handler j))
  in listen sckt (handler j0)

let server addr = server_aux addr 0


let client_aux addr srvr mlst i0 =
  let sckt = mk_udp_socket () in
  socketBind sckt addr;
  let rslt = ref (list_rev (list_sub i0 mlst)) in
  let rec  next_step i =
    if i < list_length mlst
    then
      let ith = unSOME (list_nth mlst i) in
      let msg = (i2s i) ^ "_" ^ ith in
      ignore(sendTo sckt msg srvr);
      let rec handler rsp from =
        if from = srvr then
          let tag = unSOME (s2i (tag_of_message rsp)) in
          let value = value_of_message rsp in
          if tag = i
          then (rslt := list_cons value !rslt; next_step (i + 1))
          else (ignore(sendTo sckt msg srvr); listen sckt handler)
        else listen sckt handler
      in listen sckt handler
    else list_rev !rslt
  in next_step i0

let client addr srvr mlst =
  client_aux addr srvr mlst 0

let test _d = newlock ()
