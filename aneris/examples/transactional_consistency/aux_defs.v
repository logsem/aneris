From iris.algebra Require Import auth gmap excl excl_auth frac_auth.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.transactional_consistency
     Require Import code_api user_params.

Definition Vals : Set := gset val.

Inductive local_state : Type :=
   | CanStart
   | Active (s : gset Key).