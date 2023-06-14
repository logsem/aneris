From aneris.aneris_lang Require Import resources proofmode.
From aneris.examples.snapshot_isolation.specs Require Import specs.
From aneris.examples.snapshot_isolation.examples.example2
        Require Import example2_code.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params time events resources.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code_api.

Section proof_of_code.

  Context `{!anerisG Mdl Σ, !User_params, !KVS_time, !KVSG Σ,
            !KVS_snapshot_isolation_api, !SI_resources Mdl Σ}.

End proof_of_code.