From aneris.aneris_lang Require Import ast.

Class KVS_transaction_api :=
  { TC_init_server : serializer -> val;
    TC_start : val;
    TC_read : val;
    TC_write : val;
    TC_commit : val;
    TC_init_client_proxy : serializer -> val
  }.
