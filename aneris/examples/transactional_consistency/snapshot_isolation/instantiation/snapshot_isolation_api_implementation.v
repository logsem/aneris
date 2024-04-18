From aneris.examples.transactional_consistency.snapshot_isolation
     Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency
     Require Import code_api.
From aneris.aneris_lang Require Import resources.
From aneris.examples.transactional_consistency Require Import user_params.


Global Instance KVS_snapshot_isolation_api_implementation :
        KVS_transaction_api :=
  {|
    TC_init_server := init_server;
    TC_start := start;
    TC_read := read;
    TC_write := write;
    TC_commit := commit;
    TC_init_client_proxy := init_client_proxy;
  |}.
