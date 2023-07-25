From stdpp Require Import gmap.

(** Abstract Notion of Timestamps with Total Order. *)

Section Time.


  Class KVS_time := {
    Time : Type;
    TM_lt : relation Time;
    TM_lt_TO :> StrictOrder TM_lt;
    TM_lt_tricho : ∀ m n : Time, TM_lt m n ∨ m = n ∨ TM_lt n m;
    TM_EqDecision :> EqDecision Time;
    TM_Countable :> Countable Time;
   }.


End Time.
