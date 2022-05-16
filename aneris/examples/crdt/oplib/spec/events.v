From stdpp Require Import base countable.
From aneris.aneris_lang Require Import lang.
From aneris.prelude Require Import time.
From aneris.aneris_lang.lib Require Import vector_clock_proof.
From aneris.examples.crdt.spec Require Import crdt_time crdt_events.
(* TODO: refactor this dependency so that spec/ doesn't depend on proof/ *)
From aneris.examples.crdt.oplib.proof Require Import time.

(** * Instantiation of OpLib events, which are events that use vector clocks as timestamps. *)
Section Events.

  Context `{!EqDecision LogOp, !Countable LogOp}.

  Definition cc_impl : relation (gset (Event LogOp)) :=
    λ s s',
      ∀ (e e' : Event LogOp),
        e ∈ s' → e' ∈ s' →
        e ≤_t e' ->
        e' ∈ s →
        e ∈ s.

  Global Instance cc_impl_refl : Reflexive cc_impl.
  Proof.
    intros s e e' Hin Hin' Hlt Hin''.
    done.
  Qed.

  Definition cc_subseteq : relation (gset (Event LogOp)) :=
    λ s s', s ⊆ s' ∧ cc_impl s s'.

  Global Instance cc_subseteq_preorder : PreOrder cc_subseteq.
  Proof.
    split; constructor.
    - done.
    - rewrite /cc_impl. eauto.
    - destruct H as [H _].
      destruct H0 as [H0 _].
      set_solver.
    - destruct H as [Hsub Hy].
      destruct H0 as [Hsub' Hz].
      intros e e' Hin Hin' Hle Hinx.
      assert (e' ∈ y) as He'y by set_solver.
      assert (e ∈ y) as Hey.
      { apply (Hz e e'); auto. }
      apply (Hy e e'); auto.
  Qed.

  Lemma cc_subseteq_union h h1 h2 :
    cc_subseteq h1 h -> cc_subseteq h2 h -> cc_subseteq (h1 ∪ h2) h.
  Proof.
    intros [Hsub1 Hcc1] [Hsub2 Hcc2].
    split; [set_solver |].
    intros e e' Hin Hin' Hle [Hl | Hr]%elem_of_union.
    - apply elem_of_union_l.
      apply (Hcc1 e e'); auto.
    - apply elem_of_union_r.
      apply (Hcc2 e e'); auto.
  Qed.

End Events.

Global Arguments cc_subseteq {_ _ _}.

Section ComputeMaximals.

  Context `{!EqDecision LogOp, !Countable LogOp}.

  Global Instance maximals_computing : Maximals_Computing (Event LogOp).
  Proof.
    refine {| Maximals := compute_maximals EV_Time;
              Maximum := compute_maximum EV_Time; |}.
    - apply compute_maximals_correct.
    - apply compute_maximum_correct.
  Qed.

End ComputeMaximals.

