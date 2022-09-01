From aneris.aneris_lang Require Import resources proofmode.
From iris.algebra Require Import auth csum excl agree.
From aneris.algebra Require Import monotone.
From aneris.prelude Require Import time.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_resources.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.proof Require Import utils events.
From aneris.examples.crdt.statelib.STS Require Import lst gst utils.
From iris.base_logic.lib Require Import invariants.

From aneris.examples.crdt.statelib.resources
  Require Import utils resources_inv resources_local resources_global.

Section AboutLock.
  Context `{CRDT_Op: Type,
            !anerisG Mdl Σ, !CRDT_Params,
            !EqDecision CRDT_Op, !Countable CRDT_Op,
            !StLib_GhostNames, !Internal_StLibG CRDT_Op Σ}.

  Notation princ_ev := (@principal (gset (Event CRDT_Op)) cc_subseteq).

  Definition StLib_OwnLockInv (i: RepId) (h__local h__foreign: event_set CRDT_Op): iProp Σ :=
    ∃ (f: fRepId),
      ⌜ fin_to_nat f = i ⌝
      ∗ ⌜ local_events i h__local ⌝
      ∗ ⌜ foreign_events i h__foreign ⌝
      ∗ own (γ_loc_own !!! f) ((1/3)%Qp, to_agree h__local)
      ∗ own (γ_loc_for !!! f) ((1/2)%Qp, to_agree h__foreign).

  Definition StLib_OwnLockSnap (f: fRepId) (h: event_set CRDT_Op) :=
    own (γ_loc_cc' !!! f) (◯ princ_ev h).

End AboutLock.
