(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/reliable_communication/lib/dlm/dlm_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.examples.reliable_communication Require Import client_server_code.

(**  Simple implementation of distributed lock using a boolean reference.

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
    used as advisory.  *)

Definition acquire_and_transfer : val :=
  λ: "lk" "c", acquire "lk";;
                send "c" #"acquire_OK".

Definition listen_to_client : val :=
  λ: "lk" "c",
  letrec: "loop" <> :=
    let: "msg" := recv "c" in
    (if: "msg" = #"acquire"
     then  acquire_and_transfer "lk" "c"
     else  (if: "msg" = #"release"
       then  release "lk"
       else  assert: #false));;
    "loop" #() in
    "loop" #().

Definition connections_loop : val :=
  λ: "skt" "lk",
  letrec: "loop" <> :=
    let: "new_conn" := accept "skt" in
    Fork (listen_to_client "lk" (Fst "new_conn"));;
    "loop" #() in
    "loop" #().

Definition dlock_start_service : val :=
  λ: "srv_addr",
  let: "skt" := make_server_skt string_serializer string_serializer
                "srv_addr" in
  let: "lk" := newlock #() in
  server_listen "skt";;
  connections_loop "skt" "lk".

Definition dlock_subscribe_client : val :=
  λ: "clt_addr" "srv_addr",
  let: "skt" := make_client_skt string_serializer string_serializer
                "clt_addr" in
  let: "c" := connect "skt" "srv_addr" in
  "c".

Definition dlock_acquire : val :=
  λ: "c", send "c" #"acquire";;
           recv "c";;
           #().

Definition dlock_release : val := λ: "c", send "c" #"release".
