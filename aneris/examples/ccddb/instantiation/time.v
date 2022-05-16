From aneris.examples.ccddb.spec Require Import time.
From aneris.prelude Require Import time.

Instance db_time  : DB_time :=
  {| Time := vector_clock; TM_le := vector_clock_le; TM_lt := vector_clock_lt;
     TM_lt_irreflexive := vector_clock_lt_irreflexive;
     TM_lt_TM_le := vector_clock_lt_le;
     TM_lt_exclusion := vector_clock_lt_exclusion;
     TM_le_eq_or_lt := vector_clock_le_eq_or_lt;
     TM_le_lt_trans := vector_clock_le_lt_trans;
     TM_lt_le_trans := vector_clock_lt_le_trans; |}.

Instance maximals_computing : Maximals_Computing :=
{| Maximals := @compute_maximals; Maximum := @compute_maximum;
   Maximals_correct := @compute_maximals_correct;
   Maximum_correct := @compute_maximum_correct |}.
