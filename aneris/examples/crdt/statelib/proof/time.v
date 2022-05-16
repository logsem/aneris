From stdpp Require Import gmap.
From aneris.examples.crdt.spec Require Import crdt_time.

Section Time.

  Definition RepId := nat.
  Definition SeqNum := nat.
  Definition EvId : Type := RepId * SeqNum.
  Definition Timestamp := gset EvId.

  Definition ts_le (ts1 ts2 : Timestamp) : Prop := ts1 ⊆ ts2.

  Definition ts_lt (ts1 ts2 : Timestamp) : Prop := ts1 ⊂ ts2.

  Global Instance timestamp_time : Log_Time.
  Admitted.
  (* TODO
  Global Instance timestamp_time : Log_Time :=
    {| Time := vector_clock;
       TM_le := vector_clock_le;
       TM_lt := vector_clock_lt;
       TM_lt_irreflexive := vector_clock_lt_irreflexive;
       TM_lt_TM_le := vector_clock_lt_le;
       TM_le_eq_or_lt := vector_clock_le_eq_or_lt;
       TM_le_lt_trans := vector_clock_le_lt_trans;
       TM_lt_le_trans := vector_clock_lt_le_trans; |}.
    *)

End Time.
