From iris.algebra Require Import agree auth excl gmap dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof.
Import lock_proof.


  (* ------------------------------------------------------------------------ *)
  Section Log.

  Definition inject_log `{!Inject A val} (xs : list A) :=
    ($xs, #(List.length xs))%V.

  Global Program Instance Inject_log `{!Inject A val}
    : Inject (list A) val := {| inject := inject_log |}.
  Next Obligation.
    intros ? [] xs ys. inversion 1 as [[Hinj Hinj2]].
    by apply Inject_list in Hinj.
  Qed.

  Context `[!Inject A val].

  Definition is_log (logM : list A) (logV : val) :=
    ∃ (lV : val), logV = (lV, #(List.length logM))%V ∧ is_list logM lV.

  Lemma is_log_inject xs l :
    is_log xs l ↔ l = $xs.
  Proof. Admitted.

  (* Definition is_logLoc (logM : list A) (logL : loc) : iProp Σ := *)
  (*   ∃ (logV : val), logL ↦[ip] logV ∗ ⌜is_log logM logV⌝. *)
  End Log.
