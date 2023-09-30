From iris.algebra Require Import agree auth excl gmap updates local_updates.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import lang resources resources inject.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import
     list_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import
  serialization_proof.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code
                    snapshot_isolation_code_api.
From aneris.aneris_lang Require Import resources.
From aneris.examples.reliable_communication.lib.mt_server Require Import user_params.
From aneris.examples.snapshot_isolation.specs Require Import
  user_params resources specs.
From aneris.examples.snapshot_isolation.proof.resources Require Import
  resource_algebras
  global_invariant.
From aneris.examples.snapshot_isolation.instantiation Require Import
  snapshot_isolation_api_implementation
  instantiation_of_resources.
From aneris.examples.snapshot_isolation.proof.server Require Import
  proof_of_init_server.

Global Instance SI_init_instanciation `{!anerisG Mdl Σ, !User_params} :
    SI_init.
Proof.
Admitted.
