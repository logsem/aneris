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

From aneris.examples.crdt.statelib.resources Require Import utils.

Instance timetouse: Log_Time := timestamp_time.



Section AboutGlobalInvariant.
  Context `{CRDT_Op: Type,
            !anerisG Mdl Σ, !CRDT_Params,
            !EqDecision CRDT_Op, !Countable CRDT_Op,
            !StLib_GhostNames, !Internal_StLibG CRDT_Op Σ}.
  Notation princ_ev := (@principal (gset (Event CRDT_Op)) cc_subseteq).

  Definition StLib_GlibInv_local_part (f: fRepId) (g: Gst CRDT_Op) : iProp Σ :=
    ∃ h__local h__foreign h__sub : event_set CRDT_Op,
      ⌜g.2 !!! f = h__local ∪ h__foreign⌝ ∗ ⌜
      local_events f h__local⌝ ∗ ⌜foreign_events f h__foreign⌝ ∗
      ⌜foreign_events f h__sub⌝ ∗
      ⌜h__local ∪ h__sub ⊆_cc h__local ∪ h__foreign⌝ ∗
      own (γ_loc_own !!! f) ((1 / 3)%Qp, to_agree h__local) ∗
      own (γ_loc_for !!! f) ((1 / 2)%Qp, to_agree h__foreign) ∗
      own (γ_loc_sub !!! f) ((1 / 3)%Qp, to_agree h__sub) ∗
      own (γ_loc_cc !!! f) (● princ_ev (h__local ∪ h__sub)) ∗
      own (γ_loc_cc' !!! f) (● princ_ev (h__local ∪ h__foreign)).

  Definition StLib_GlobalInv : iProp Σ :=
    inv CRDT_InvName
      (∃ (g: Gst CRDT_Op), own γ_global ((1/3)%Qp, to_agree g.1)
      ∗ own γ_global_snap (● g.1)
      ∗ ⌜ Gst_Validity g ⌝
      ∗ ∃ (S: gset (fRepId)),
        (∀ (f: fRepId), ⌜f ∈ S⌝)
        ∗ [∗ set] k ∈ S,
          StLib_GlibInv_local_part k g).
  Global Instance StLib_GlobalInv_persistent : Persistent StLib_GlobalInv := _.
End AboutGlobalInvariant.


