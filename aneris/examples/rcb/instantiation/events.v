From stdpp Require Import base gmap.
From aneris.examples.rcb.spec Require Import events.
From aneris.examples.rcb.model Require Import events.

Instance rcb_events : RCB_events :=
  { ge := global_event;
    GE_payload := ge_payload;
    GE_vc := ge_time;
    GE_origin := ge_orig;

    le := local_event;
    LE_payload := le_payload;
    LE_vc := le_time;
    LE_origin := le_orig;

    erasure :=  erase;
    erasure_payload := erase_payload;
    erasure_vc := erase_time;
    erasure_origin := erase_orig
  }.
