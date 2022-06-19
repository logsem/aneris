From iris.algebra Require Import excl.
From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang Require Import tactics proofmode.
From aneris.aneris_lang.program_logic
     Require Import aneris_weakestpre aneris_lifting.
From aneris.aneris_lang.lib Require Import assert_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.prelude
     Require Import ser_inj.
From aneris.examples.reliable_communication.lib.dlm
     Require Import dlm_code.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code model.
From aneris.examples.reliable_communication.lib.dlm
     Require Import dlm_prelude dlm_resources dlm_code dlm_spec.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import
     ras events resources api_spec.
From aneris.examples.reliable_communication.examples.dlm_db_example
     Require Import dlm_db_example_code.




Lemma db_init_empty `{!anerisG Mdl Σ, DB : !DB_params, !DBPreG Σ } : DB_init.
Proof.
  (* iMod (own_alloc (● (∅ : gmapUR socket_address (agreeR gnameO)))) as (γknwF) "Hknw"; *)
  (*   first by apply auth_auth_valid. *)
  (* iMod (own_alloc (● (GSet ∅ : (gset_disjUR socket_address)))) as (γfreF) "Hfre"; *)
  (*   first by apply auth_auth_valid. *)
  (* set (db := *)
  (*        {| *)
  (*          DBG_known_replog_name := γknwF; *)
  (*          DBG_free_replog_set_name := γfreF *)
  (*        |}). *)
Admitted.
