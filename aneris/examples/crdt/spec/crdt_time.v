From stdpp Require Import gmap.

(** * Logical time *)

Section Time.

  Class Log_Time := {
    Time : Type;
    Time_EqDecision :> EqDecision Time;
    Time_Countable :> Countable Time;

    TM_le : relation Time;
    TM_le_PO :> PartialOrder TM_le;

    TM_lt : relation Time;
    TM_lt_irreflexive :> Irreflexive TM_lt;
    TM_lt_trans :> Transitive TM_lt;
    TM_lt_decision :> ∀ ts ts', Decision (TM_lt ts ts');

    TM_lt_TM_le : ∀ ts ts', TM_lt ts ts' → TM_le ts ts';
    TM_le_eq_or_lt : ∀ ts ts', TM_le ts ts' → ts = ts' ∨ TM_lt ts ts';
    TM_le_lt_trans :
      ∀ ts ts' ts'', TM_le ts ts' → TM_lt ts' ts'' → TM_lt ts ts'';
    TM_lt_le_trans :
      ∀ ts ts' ts'', TM_lt ts ts' → TM_le ts' ts'' → TM_lt ts ts'';
  }.

  Lemma TM_lt_exclusion `{!Log_Time} (ts ts' : Time) : TM_lt ts ts' → TM_lt ts' ts → False.
  Proof.
    intros Hlt1 Hlt2.
    pose proof (TM_lt_trans _ _ _ Hlt1 Hlt2) as Hlt3.
    eapply TM_lt_irreflexive; eauto.
  Qed.

  Definition TM_incomparable `{!Log_Time} ts ts' :=
    ¬ TM_le ts ts' ∧ ¬ TM_le ts' ts.

  Class Timed `{!Log_Time} (T : Type) := time : T → Time.

End Time.

Notation "s '<_t' t" :=
  (TM_lt (time s) (time t)) (at level 70, no associativity).
Notation "s '≤_t' t" :=
  (TM_le (time s) (time t)) (at level 70, no associativity).
Notation "s '=_t' t" :=
  (time s = time t) (at level 70, no associativity).

Section Maximals.

  Context `{T : Type, !EqDecision T, !Countable T, !Log_Time, !Timed T}.

  (* An event e is maximal w.r.t a set of events S if
     (1) e is in S and
     (2) no event in the set has e as a causal dependency.
         i.e. if no event in S sees e. *)
  Definition maximal (e : T) (s : gset T) : Prop :=
    e ∈ s ∧ ∀ e', e' ∈ s -> ¬ (e <_t e').

  Lemma maximal_union (e e' : T) (s : gset T) :
    maximal e s -> not (e <_t e') -> maximal e (s ∪ {[ e' ]}).
  Proof.
    intros [Hin Hmax] Hnot.
    split; [set_solver |].
    intros e'' [Hinl | ->%elem_of_singleton]%elem_of_union Hcontra.
    - by (eapply Hmax).
    - by apply Hnot.
  Qed.

  Lemma maximal_union_inv (e e' : T) (s : gset T) :
    maximal e (s ∪ {[ e' ]}) -> e ∈ s -> maximal e s.
  Proof.
    intros [_ Hmax] Hins.
    split; [set_solver |].
    intros e'' Hins''.
    apply Hmax; set_solver.
  Qed.

  (* Does the set `Y` consist of the elements in `X` maximal wrt `<_t`? *)
  Definition is_maximals (X Y : gset T) :=
    ∀ t : T, t ∈ Y ↔ maximal t X.

  (* Is `mx` an upper bound of `X`? *)
  Definition is_maximum (mx : T) (X : gset T) :=
    mx ∈ X ∧ ∀ t, t ∈ X → (¬ t = mx) → t <_t mx.

  Class Maximals_Computing :=
    {
      Maximals : gset T -> gset T;
      Maximals_correct : ∀ (X : gset T), is_maximals X (Maximals X);
      Maximum : gset T -> option T;
      Maximum_correct : ∀ (X : gset T),
          (∀ x y, x ∈ X → y ∈ X → x =_t y → x = y) →
          (∀ x, Maximum X = Some x ↔ is_maximum x X);
    }.

  Lemma is_maximum_maximal x S : is_maximum x S -> maximal x S.
  Proof.
    intros [Hin Hmax].
    split; [done |].
    intros e' Hin' contra.
    destruct (decide (x = e')) as [-> | Hne].
    - eapply TM_lt_irreflexive; eauto.
    - assert (e' ≠ x) as Hne'; [done |].
      pose proof (Hmax e' Hin' Hne') as Hlt.
      assert (x <_t x) as Hirr.
      { eapply TM_lt_trans; eauto. }
      eapply TM_lt_irreflexive; eauto.
  Qed.

End Maximals.

Arguments Maximals_Computing (T) {_ _ _ _}.
