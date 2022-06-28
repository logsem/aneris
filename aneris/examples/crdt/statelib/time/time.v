From stdpp Require Import gmap.
From aneris.examples.crdt.spec Require Import crdt_time.
From aneris.examples.crdt.statelib.proof Require Import utils.

Section Time.
  Definition ts_le (ts1 ts2 : Timestamp) : Prop :=
    ts1 ⊆ ts2.

  Definition ts_lt := strict ts_le.

  Lemma ts_lt_irreflexive: ∀ x: Timestamp, ~ ts_lt x x.
  Proof. by intros s [H H']. Qed.
  Lemma ts_lt_trans: ∀ x y z, ts_lt x y → ts_lt y z → ts_lt x z.
  Proof. set_solver. Qed.
  Lemma ts_lt_TM_le: ∀ x x', ts_lt x x' → ts_le x x'.
  Proof. exact strict_include. Qed.

  Lemma ts_le_eq_or_lt: ∀ x x', ts_le x x' → x = x' ∨ ts_lt x x'.
  Proof.
    intros ???.
    destruct (set_subseteq_inv x x' H);
    [by right | left; by apply set_eq].
  Qed.

  Lemma ts_le_lt_trans: 
    ∀ t t' t'' : Timestamp,
                       ts_le t t' → ts_lt t' t'' → ts_lt t t''.
  Proof. set_solver. Qed.

  Lemma ts_lt_le_trans: 
    ∀ t t' t'' : Timestamp,
                       ts_lt t t' → ts_le t' t'' → ts_lt t t''.
  Proof. set_solver. Qed.

  Global Instance ts_le_trans: Transitive ts_le.
  Proof. intros?. set_solver.  Qed.
  Global Instance ts_le_refl: Reflexive ts_le.
  Proof. intros ?. set_solver.  Qed.

  Global Instance ts_lt_asym: Asymmetric ts_lt.
  Proof. intros?. set_solver. Qed.

  Global Instance timestamp_time : Log_Time :=
    {| Time := Timestamp;
       TM_le := ts_le;
       TM_le_PO := set_subseteq_partialorder;
       TM_lt := ts_lt;
       TM_lt_irreflexive := ts_lt_irreflexive;
       TM_lt_trans := ts_lt_trans;
       TM_le_eq_or_lt := ts_le_eq_or_lt;
       TM_lt_TM_le := ts_lt_TM_le;
       TM_le_lt_trans := ts_le_lt_trans;
       TM_lt_le_trans := ts_lt_le_trans
    |}.

End Time.
