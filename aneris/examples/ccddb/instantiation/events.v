From stdpp Require Import base gmap.
From aneris.examples.ccddb.spec Require Import time events.
From aneris.examples.ccddb.model Require Import events.
From aneris.examples.ccddb.instantiation Require Import time.

Instance we_timed : Timed write_event := we_time.
Instance ae_timed : Timed apply_event := ae_time.

Instance db_events : DB_events :=
  { we := write_event;
    WE_val := we_val;
    WE_timed := we_timed;
    ae := apply_event;
    AE_val := ae_val;
    AE_key := ae_key;
    AE_timed := ae_timed;
    erasure :=  erase;
    erasure_time := erase_time;
    erasure_val:= erase_val; }.
