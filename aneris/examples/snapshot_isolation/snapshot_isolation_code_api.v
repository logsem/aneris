
From aneris.aneris_lang Require Import ast.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code.


Class KVS_snapshot_isolation_api :=
  { SI_init_server : serializer -> val;
    SI_start : val;
    SI_read : val;
    SI_write : val;
    SI_commit : val;
    SI_init_client_proxy : serializer -> val
  }.
