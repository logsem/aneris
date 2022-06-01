From stdpp Require Import gmap.

(** Abstract Notion of Timestamps with Total Order. *)

Section Time.


  Class DB_time := {
    Time : Type;
    TM_lt : relation Time;
    TM_lt_TO :> StrictOrder TM_lt;
    TM_lt_tricho : ∀ m n : Time, TM_lt m n ∨ m = n ∨ TM_lt n m;
    TM_EqDecision :> EqDecision Time;
    TM_Countable :> Countable Time;
    (* TM_max : Time → Time → Time. TODO *)
   }.

  (* Class Timed {dbt: DB_time} (T : Type) := time : T → Time. *)

  (* Notation "s '<ₜ' t" := *)
  (*   (TM_lt (time s) (time t)) (at level 70, no associativity). *)
  (* Notation "t1 '≤ₜ' t2" := *)
  (*   (TM_lt (time t1) (time t2) ∨ (time t1 = time t2)) *)
  (*     (at level 70, no associativity). *)
  (* Notation "t1 '=ₜ' t2" := *)
  (*   (time t1 = time t2) (at level 70, no associativity). *)
  End Time.

(*
Notation "s '<ₜ@{' d '}' t" :=
  (TM_lt (@time d _ _ s) (@time d _ _ t))
    (at level 70, no associativity, format "s  '<ₜ@{' d '}'  t").
Notation "s '≤ₜ@{' d '}' t" :=
  (TM_lt (@time d _ _ s) (@time d _ _ t) ∨  (@time d _ _ s) = (@time d _ _ t))
    (at level 70, no associativity, format "s  '≤ₜ@{' d '}'  t").
Notation "s '=ₜ@{' d '}' t" :=
  ((@time d _ _ s) = (@time d _ _ t))
    (at level 70, no associativity, format "s  '=ₜ@{' d '}'  t").
*)

(* Notation "s '<ₜ' t" := *)
(*   (TM_lt (time s) (time t)) (at level 70, no associativity). *)
(* Notation "s '≤ₜ' t" := *)
(*   (TM_lt (time s) (time t) ∨ (time s = time t)) (at level 70, no associativity). *)
(* Notation "s '=ₜ' t" := *)
(*   (time s = time t) (at level 70, no associativity). *)
