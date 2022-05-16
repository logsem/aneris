From stdpp Require Import gmap.

(** Abstract Notion of Timestamps with Total Order. *)

Section Time.

  Class DB_time := {
    Time : Type;
    TM_lt' : relation Time;
    TM_lt := strict TM_lt';
    TM_lt_TO :> TotalOrder (TM_lt);
    TM_EqDecision :> EqDecision Time;
   }.

  Class Timed {dbt: DB_time} (T : Type) := time : T → Time.

  Notation "t1 '<ₜ' t2" :=
    (TM_lt (time t1) (time t2)) (at level 70, no associativity).
  Notation "t1 '≤ₜ' t2" :=
    (TM_lt (time t1) (time t2) ∨ (time t1 = time t2)) (at level 70, no associativity).
  Notation "t1 '=ₜ' t2" :=
    (time t1 = time t2) (at level 70, no associativity).

  Definition IsMaximum {T : Type} `{!DB_time} `{!EqDecision T}
             `{!Countable T} `{!Timed T} (X : gset T) (mx : T) :=
    mx ∈ X ∧ ∀ t, t ∈ X → (¬ t = mx) → t <ₜ mx.

  Class Maximals_Computing `{!DB_time} :=
    {
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
  (TM_lt (@time d _ _ s) (@time d _ _ t) ∨  (@time d _ _ s) = (@time d _ _ t))
    (at level 70, no associativity, format "s  '≤ₜ@{' d '}'  t").
Notation "s '=ₜ@{' d '}' t" :=
  ((@time d _ _ s) = (@time d _ _ t))
    (at level 70, no associativity, format "s  '=ₜ@{' d '}'  t").

Notation "s '<ₜ' t" :=
  (TM_lt (time s) (time t)) (at level 70, no associativity).
Notation "s '≤ₜ' t" :=
  (TM_lt (time s) (time t) ∨ (time s = time t)) (at level 70, no associativity).
Notation "s '=ₜ' t" :=
  (time s = time t) (at level 70, no associativity).
