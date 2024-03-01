From aneris.examples.transactional_consistency.snapshot_isolation
     Require Import snapshot_isolation_code
                    snapshot_isolation_code_api.
From aneris.aneris_lang Require Import resources.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  user_params.

Global Instance KVS_snapshot_isolation_api_implementation :
        KVS_snapshot_isolation_api :=
  {|
    SI_init_server := init_server;
    SI_start := start;
    SI_read := read;
    SI_write := write;
    SI_commit := commit;
    SI_init_client_proxy := init_client_proxy;
  |}.
