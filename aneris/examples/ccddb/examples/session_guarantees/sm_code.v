From iris Require Import invariants.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import lang network tactics.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.examples Require Import res.

(* A simple session manager to reason about session guarantees *)
Section Code.
  Context `{!DB_params}.

  (* A version of listen_wait that additionally waits to receive a message
     with the given sequence id.
   *)
  Definition listen_wait_for_seqid : val :=
    rec: "listen_wait_for_seqid" "sh" "seq_id" :=
        let: "resp_msg" := unSOME (ReceiveFrom "sh") in
        let: "resp" := s_deser (s_serializer resp_serialization) (Fst "resp_msg") in
        let: "tag" := Fst "resp" in
        let: "val" := Snd "resp" in
        if: "tag" = !"seq_id" then
          ("seq_id" <- !"seq_id" + #1;;
          "val")
        else
          ("listen_wait_for_seqid" "sh" "seq_id").

  (*
   * Executes a request within a session.
   * The execution can be conceptualized as a
   * sequence of steps:
   *   - increment the sequence id
   *   - send an arbitrary message to a server
   *   - loop waiting for a reply from the server, using the sequence id to
   *     match the request we just sent to its response
   *   - return the server's response, minus the sequence id
   *)
  Definition session_exec : val :=
    λ: "sh" "seq_id" "lock" "server_addr" "req",
      acquire "lock";;
      let: "msg" := s_ser (s_serializer req_serialization) (!"seq_id", "req") in
      SendTo "sh" "msg" "server_addr";;
      let: "ret" :=  (listen_wait_for_seqid "sh" "seq_id") in
      release "lock";;
      "ret".

  (*
   * Initializes the session manager.
   * Returns a tuple `(init_fn, read_fn, write_fn)` of closures containing
   * the init_session, read and write operations, respectively.
   *
   * Throughout all operations, we maintain a _sequence id_, a monotonically
   * increasing integer that counts the number of requests sent to the server
   * so far in the session.
   * Calls to init_session, reads and writes all increase the sequence id.
   *
   * Inits, reads and writes are synchronized with a lock to guarantee that the
   * sequence id observed by an operation remains the maximum among all
   * previously-seen sequence ids, throughout the
   * execution of the operation. This is important because we communicate over
   * UDP so there are no duplicate protection or ordering guarantees.
   *)
  Definition sm_setup : val :=
    λ: "client_addr",
      let: "socket" := NewSocket in
      SocketBind "socket" "client_addr";;
      let: "seq_id" := ref #0 in
      let: "lock" := newlock #() in

      (* Initializes a session with the replica at `server_addr`. *)
      let: "init_fn" :=
         λ: "server_addr",
           session_exec "socket" "seq_id" "lock" "server_addr" (InjL #"I");;
           #()
      in
      (* Reads the value of `key` from the replica at `server_addr`. *)
      let: "read_fn" :=
         λ: "server_addr" "key",
         let: "res" := session_exec "socket" "seq_id" "lock" "server_addr" (InjR (InjL "key")) in
         match: "res" with
           InjL "x" => assert #false
         | InjR "res'" =>
           match: "res'" with
             InjL "vo" =>
             match: "vo" with
               InjL "x" => NONEV
             | InjR "v" => (SOME "v")%V
             end
           | InjR "x" => assert #false
           end
         end
      in
      (* Writes `val` to `key` in the replica at `server_addr`. *)
      let: "write_fn" :=
         λ: "server_addr" "key" "val",
          session_exec "socket" "seq_id" "lock" "server_addr" (InjR (InjR ("key", "val")));;
          #()
      in
      ("init_fn", "read_fn", "write_fn").

End Code.
