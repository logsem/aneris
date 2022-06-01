From aneris.aneris_lang Require Import lang.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import time.


Global Instance int_time : DB_time :=
  {| Time := nat;
    TM_lt := Nat.lt;
    TM_lt_tricho := PeanoNat.Nat.lt_trichotomy |}.
