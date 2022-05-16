From stdpp Require Import gmap.
From aneris.aneris_lang Require Import lang.
From aneris.examples.ccddb.spec Require Import base time.

(** Write and apply events *)

Section Events.
  Context `{!DB_time}.

  Class DB_events :=
    {
      (** Write events *)

      we : Type;
      WE_val : we → val;
      WE_timed :> Timed we;
      WE_EqDecision :> EqDecision we;
      WE_Countable :> Countable we;

      (** Apply events *)

      ae : Type;
      AE_key : ae → Key;
      AE_val : ae → val;
      AE_timed :> Timed ae;
      AE_EqDecision :> EqDecision ae;
      AE_Countable :> Countable ae;

      (** Erasure events *)

      erasure : ae → we;
      erasure_val: ∀ (e : ae), (erasure e).(WE_val) = e.(AE_val);
      erasure_time: ∀ (e : ae), (erasure e) =ₜ e;
    }.

  (** Aliases for sets of events *)

  Context `{!DB_events}.

  Notation gmem := (gset we).
  Notation lhst := (gset ae).
  Definition restrict_key (k : Key) (s : lhst)
    : gset ae := filter (λ x, AE_key x = k) s.

  Definition seen_relation : relation lhst :=
    λ s s', s ⊆ s' ∧
            ∀ ae ae',
              ae ∈ s' → ae' ∈ s' → ae <ₜ ae' → ae' ∈ s → ae ∈ s.

End Events.

Notation gmem := (gset we).
Notation lhst := (gset ae).
