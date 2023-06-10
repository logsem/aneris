
From aneris.aneris_lang Require Import ast.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code.


Class KVS_snapshot_isolation_api :=
  { SI_init_server : serializer -> val;
    SI_start : val;
    SI_read : val;
    SI_write : val;
    SI_commit : val;
    SI_run : val;
    SI_init_client_proxy : serializer -> val
 }.

(* TODO: move to the instantiation folder when ready. *)
(*
Global Instance KVS_snapshot_isolation_api_implementation : KVS_snapshot_isolation_api :=
  {| SI_init_server := init_server;
    SI_start := start;
    SI_read := read;
    SI_write := write;
    SI_commit := commit;
    SI_run := run;
    SI_init_client_proxy := init_client_proxy;
 |}.
*)
