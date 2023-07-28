From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code
                    snapshot_isolation_code_api.
From aneris.aneris_lang Require Import resources.
From aneris.examples.snapshot_isolation.specs Require Import user_params specs.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.

Global Instance SI_init_instanciation `{!anerisG Mdl Σ, !User_params} :
    SI_init.
Proof.
Admitted.
