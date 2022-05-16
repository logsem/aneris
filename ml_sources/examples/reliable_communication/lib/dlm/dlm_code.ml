open Ast
open Serialization_code
open Client_server_code

(** Simple implementation of distributed lock using a boolean reference.

    The implementation is naive in several regards:

    [L2] the lock server is not fault-tolerant
    [L3] the clients are assumed not to crash as well; if the client
    crash, while holding the lock, the whole service will be blocked.
    [L4] no explicit lock modes, e.g. read-only, write-only, etc.
    [L5] the lock is spin lock, no priority is given.


    [L2] One ce we have Viewstamped replication, we can actually replicate the
    lock service!
    [L3] This is new and potentially challenging - to explore.
    To account for the client crashes, the lock should store the identity of
    the current holder of the lock together with a limited time lease after
    expiration of which the lock must be either released by the client, or
    the server discards the clients rights to the lock.
    [L4] Relatively easy
    [L5] Can be ported from existing proofs in Iris on ticket locks, etc.

    Note that the lock can be used as advisory, and in some cases can only be
    used as advisory. *)

type dlock = (string, string) chan_descr

let acquire_and_transfer (lk : Mutex.t) (c : dlock) =
  acquire lk; send c "acquire_OK"

let listen_to_client (lk : Mutex.t) (c : dlock) =
  let rec loop () =
    begin
      let msg = recv c in
      if msg = "acquire" then acquire_and_transfer lk c
      else if msg = "release" then release lk
      else assert false
    end;
    loop ()
  in loop ()

let connections_loop (skt : (string, string) server_skt) (lk : Mutex.t) =
  let rec loop () =
    let new_conn = accept skt in
    fork (listen_to_client lk) (fst new_conn);
    loop ()
  in loop ()

let dlock_start_service (srv_addr : saddr) =
  let skt = make_server_skt string_serializer string_serializer srv_addr in
  let lk = newlock () in
  server_listen skt;
  connections_loop skt lk

let dlock_subscribe_client (clt_addr : saddr) (srv_addr : saddr) =
  let skt = make_client_skt string_serializer string_serializer clt_addr in
  let c = connect skt srv_addr in c

let dlock_acquire (c : dlock) = send c "acquire"; ignore (recv c)

let dlock_release (c : dlock) = send c "release"
