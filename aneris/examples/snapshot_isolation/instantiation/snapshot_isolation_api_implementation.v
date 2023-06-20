From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code 
                    snapshot_isolation_code_api.

Global Instance KVS_snapshot_isolation_api_implementation :
        KVS_snapshot_isolation_api :=
  {|
    SI_init_server := init_server;
    SI_start := start;
    SI_read := read;
    SI_write := write;
    SI_commit := commit;
    SI_run := run;
    SI_init_client_proxy := init_client_proxy;
  |}.

