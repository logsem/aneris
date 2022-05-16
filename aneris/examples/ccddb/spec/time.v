From stdpp Require Import gmap.

(** Abstraction of the vector clocks. *)

Section Time.

  Class DB_time := {
    Time : Type;
    TM_le : relation Time;
    TM_le_PO :> PartialOrder TM_le;
    TM_lt : relation Time;
    TM_lt_irreflexive : ∀ vc, ¬ TM_lt vc vc;
    TM_lt_trans :> Transitive TM_lt;
    TM_lt_TM_le : ∀ vc vc', TM_lt vc vc' → TM_le vc vc';
    TM_lt_exclusion : ∀ vc vc', TM_lt vc vc' → TM_lt vc' vc → False;
    TM_le_eq_or_lt : ∀ vc vc', TM_le vc vc' → vc = vc' ∨ TM_lt vc vc';
    TM_le_lt_trans :
      ∀ vc vc' vc'', TM_le vc vc' → TM_lt vc' vc'' → TM_lt vc vc'';
    TM_lt_le_trans :
      ∀ vc vc' vc'', TM_lt vc vc' → TM_le vc' vc'' → TM_lt vc vc'';
 }.

  Definition TM_incomparable `{!DB_time} vc vc' :=
    ¬ TM_le vc vc' ∧ ¬ TM_le vc' vc.

  Class Timed {dbt: DB_time} (T : Type) := time : T → Time.

  Notation "s '<ₜ' t" :=
    (TM_lt (time s) (time t)) (at level 70, no associativity).
  Notation "s '≤ₜ' t" :=
    (TM_le (time s) (time t)) (at level 70, no associativity).
  Notation "s '=ₜ' t" :=
    (time s = time t) (at level 70, no associativity).

  Definition IsMaximals {T : Type} `{!DB_time} `{!EqDecision T}
             `{!Countable T} `{!Timed T} (X Y : gset T) :=
    ∀ t : T, t ∈ Y ↔ t ∈ X ∧ ∀ t' : T, t' ∈ X → ¬ (t <ₜ t').

  Definition IsMaximum {T : Type} `{!DB_time} `{!EqDecision T}
             `{!Countable T} `{!Timed T} (X : gset T) (mx : T) :=
    mx ∈ X ∧ ∀ t, t ∈ X → (¬ t = mx) → t <ₜ mx.

  Class Maximals_Computing `{!DB_time} :=
    {
      Maximals : ∀ {T : Type} `{!EqDecision T} `{!Countable T}
           `{!Timed T} (X : gset T), gset T;
      Maximals_correct : ∀ {T : Type} `{!EqDecision T} `{!Countable T}
           `{!Timed T} (X : gset T), IsMaximals X (Maximals X);
      Maximum : ∀ {T : Type} `{!EqDecision T} `{!Countable T}
           `{!Timed T} (X : gset T), option T;
      Maximum_correct : ∀ {T : Type} `{!EqDecision T} `{!Countable T}
           `{!Timed T} (X : gset T),
          (∀ x y, x ∈ X → y ∈ X → x =ₜ y → x = y) →
          (∀ x, Maximum X = Some x ↔ IsMaximum X x);
    }.

  End Time.


Notation "s '<ₜ@{' d '}' t" :=
  (TM_lt (@time d _ _ s) (@time d _ _ t))
    (at level 70, no associativity, format "s  '<ₜ@{' d '}'  t").
Notation "s '≤ₜ@{' d '}' t" :=
  (TM_le (@time d _ _ s) (@time d _ _ t))
    (at level 70, no associativity, format "s  '≤ₜ@{' d '}'  t").
Notation "s '=ₜ@{' d '}' t" :=
  ((@time d _ _ s) = (@time d _ _ t))
    (at level 70, no associativity, format "s  '=ₜ@{' d '}'  t").

Notation "s '<ₜ' t" :=
  (TM_lt (time s) (time t)) (at level 70, no associativity).
Notation "s '≤ₜ' t" :=
  (TM_le (time s) (time t)) (at level 70, no associativity).
Notation "s '=ₜ' t" :=
  (time s = time t) (at level 70, no associativity).
