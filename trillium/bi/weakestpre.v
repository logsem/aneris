From stdpp Require Export coPset.
From iris.bi Require Import interface derived_connectives.
From trillium.program_logic Require Import language.
From iris.prelude Require Import options.

Inductive stuckness := NotStuck | MaybeStuck.

Definition stuckness_leb (s1 s2 : stuckness) : bool :=
  match s1, s2 with
  | MaybeStuck, NotStuck => false
  | _, _ => true
  end.
#[global] Instance stuckness_le : SqSubsetEq stuckness := stuckness_leb.
#[global] Instance stuckness_le_po : PreOrder stuckness_le.
Proof. split; by repeat intros []. Qed.

Definition stuckness_to_atomicity (s : stuckness) : atomicity :=
  if s is MaybeStuck then StronglyAtomic else WeaklyAtomic.

(** Weakest preconditions [WP e @ s ; E {{ Φ }}] have an additional argument [s]
of arbitrary type [A], that can be chosen by the one instantiating the [Wp] type
class. This argument can be used for e.g. the stuckness bit (as in Iris) or
thread IDs (as in iGPS).

For the case of stuckness bits, there are two specific notations
[WP e @ E {{ Φ }}] and [WP e @ E ?{{ Φ }}], which forces [A] to be [stuckness],
and [s] to be [NotStuck] or [MaybeStuck].  This will fail to typecheck if [A] is
not [stuckness].  If we ever want to use the notation [WP e @ E {{ Φ }}] with a
different [A], the plan is to generalize the notation to use [Inhabited] instead
to pick a default value depending on [A]. *)
Class Wp (Λ : language) (PROP A : Type) :=
  wp : A → coPset -> locale Λ -> expr Λ → (val Λ → PROP) → PROP.
Arguments wp {_ _ _ _} _ _ _ _%E _%I.
#[global] Instance: Params (@wp) 8 := {}.

(** Notations for partial weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)


Notation "'WP' e @ s ; tid ; E {{ Φ } }" := (wp s E tid e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ tid ; E {{ Φ } }" := (wp NotStuck E tid e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ tid ; E ? {{ Φ } }" := (wp MaybeStuck E tid e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ tid {{ Φ } }" := (wp NotStuck ⊤ tid e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ tid ? {{ Φ } }" := (wp MaybeStuck ⊤ tid e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'WP' e @ s ; tid ; E {{ v , Q } }" := (wp s E tid e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[          ' @  s ;  tid ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'WP' e @ tid ; E {{ v , Q } }" := (wp NotStuck E tid e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[       ' @  tid ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'WP' e @ tid ; E ? {{ v , Q } }" := (wp MaybeStuck E tid e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[        ' @  tid ;  E  ? {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'WP' e @ tid {{ v , Q } }" := (wp NotStuck ⊤ tid e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  @ tid  '/' '[   ' {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'WP' e @ tid ? {{ v , Q } }" := (wp MaybeStuck ⊤ tid e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  @ tid  '/' '[    ' ? {{  v ,  Q  } } ']' ']'") : bi_scope.

(* Texan triples *)
Notation "'{{{' P } } } e @ tid ; s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ tid ; s; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @ tid ;  s ;  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ tid ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ tid ; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @ tid ;  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ tid ; E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ tid ; E ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @ tid ;  E  ? {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ tid {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ tid {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e @ tid '/' {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ tid ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ tid ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  @ tid '/' ? {{{  x  ..  y ,   RET  pat ;  Q  } } } ']'") : bi_scope.

Notation "'{{{' P } } } e @ s ; tid ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; tid ; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @ s ; tid  ; E  {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ tid ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ tid ; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @ tid ; E  {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ tid ; E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ tid ; E ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @ tid ; E  ? {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ tid {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ tid {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e @ tid '/' {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ tid ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ tid ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e @ tid '/' ? {{{  RET  pat ;  Q  } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'{{{' P } } } e @ s ; tid ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; tid ; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ tid ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ tid ; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ tid ; E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ tid ; E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ tid {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ tid {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ tid ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ tid ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ s ; tid ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; tid; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ tid ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ tid; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ tid ; E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ tid; E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ tid {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ tid {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ tid ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ tid ?{{ Φ }}) : stdpp_scope.



(* Notation "'WP' e @ s ; E {{ Φ } }" := (wp s E e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'WP' e @ E {{ Φ } }" := (wp NotStuck E e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'WP' e @ E ? {{ Φ } }" := (wp MaybeStuck E e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'WP' e {{ Φ } }" := (wp NotStuck ⊤ e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(* Notation "'WP' e ? {{ Φ } }" := (wp MaybeStuck ⊤ e%E Φ) *)
(*   (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)

(* (** Notations with binder.  The indentation for the inner format block is chosen *)
(* such that *if* one has a single-character mask (e.g. [E]), the second line *)
(* should align with the binder(s) on the first line. *) *)
(* Notation "'WP' e @ s ; E {{ v , Q } }" := (wp s E e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[' 'WP'  e  '/' '[          ' @  s ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope. *)
(* Notation "'WP' e @ E {{ v , Q } }" := (wp NotStuck E e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[' 'WP'  e  '/' '[       ' @  E  {{  v ,  Q  } } ']' ']'") : bi_scope. *)
(* Notation "'WP' e @ E ? {{ v , Q } }" := (wp MaybeStuck E e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[' 'WP'  e  '/' '[        ' @  E  ? {{  v ,  Q  } } ']' ']'") : bi_scope. *)
(* Notation "'WP' e {{ v , Q } }" := (wp NotStuck ⊤ e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[' 'WP'  e  '/' '[   ' {{  v ,  Q  } } ']' ']'") : bi_scope. *)
(* Notation "'WP' e ? {{ v , Q } }" := (wp MaybeStuck ⊤ e%E (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[' 'WP'  e  '/' '[    ' ? {{  v ,  Q  } } ']' ']'") : bi_scope. *)

(* (* Texan triples *) *)
(* Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' {{{  P  } } }  '/  ' e  '/' @  s ;  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope. *)
(* Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope. *)
(* Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  ? {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope. *)
(* Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' {{{  P  } } }  '/  ' e  '/' {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope. *)
(* Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' {{{  P  } } }  '/  ' e  '/' ? {{{  x  ..  y ,   RET  pat ;  Q  } } } ']'") : bi_scope. *)

(* Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; E {{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' {{{  P  } } }  '/  ' e  '/' @  s ;  E  {{{  RET  pat ;  Q  } } } ']'") : bi_scope. *)
(* Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  {{{  RET  pat ;  Q  } } } ']'") : bi_scope. *)
(* Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E ?{{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  ? {{{  RET  pat ;  Q  } } } ']'") : bi_scope. *)
(* Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' {{{  P  } } }  '/  ' e  '/' {{{  RET  pat ;  Q  } } } ']'") : bi_scope. *)
(* Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e ?{{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' {{{  P  } } }  '/  ' e  '/' ? {{{  RET  pat ;  Q  } } } ']'") : bi_scope. *)

(* (** Aliases for stdpp scope -- they inherit the levels and format from above. *) *)
(* Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }}) : stdpp_scope. *)
(* Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }}) : stdpp_scope. *)
(* Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }}) : stdpp_scope. *)
(* Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }}) : stdpp_scope. *)
(* Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }}) : stdpp_scope. *)
(* Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; E {{ Φ }}) : stdpp_scope. *)
(* Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }}) : stdpp_scope. *)
(* Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E ?{{ Φ }}) : stdpp_scope. *)
(* Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }}) : stdpp_scope. *)
(* Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e ?{{ Φ }}) : stdpp_scope. *)
