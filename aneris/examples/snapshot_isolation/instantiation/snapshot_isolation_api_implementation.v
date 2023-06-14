From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params time events resources specs.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code_api.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.

Section implementation.

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

  Context `{!anerisG Mdl Σ, !User_params, !KVS_time}.

  Global Instance SI_implementation_init : SI_init.
  Proof.
    (* TODO *)
  Admitted.

End implementation.