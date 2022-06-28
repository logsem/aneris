From stdpp Require Import gmap.
From aneris.aneris_lang Require Import lang resources.
From aneris.examples.crdt.spec Require Import crdt_time.
From aneris.examples.crdt.statelib.proof Require Import utils.
From Coq.Logic Require Import Decidable.

(** Implementation of Log_Time base don the event id (EvId != RepId * SeqNum) *)

Section EVTime.
  Lemma evid_lt_irreflexive: ∀ x: EvId, ~ evid_lt x x.
  Proof. intros?[??]; eauto. Qed.

  Lemma evid_lt_trans: ∀ x y z, evid_lt x y → evid_lt y z → evid_lt x z.
  Proof.
    intros [rid sid] [rid' sid'] [rid'' sid''] [[-> Hle] Hnle][[<- Hle'] Hnle'].
    split; first by apply evid_le_trans with (rid', sid').
    intros [_ Hle_].
    destruct Hnle. split; [ reflexivity | by apply le_trans with sid'' ].
  Qed.

  Lemma evid_lt_TM_le: ∀ x x', evid_lt x x' → evid_le x x'.
  Proof. by intros ??[? _]. Qed.

  Lemma evid_le_eq_or_lt: ∀ x x', evid_le x x' → x = x' ∨ evid_lt x x'.
  Proof.
    intros[rid sid][rid' sid'][-> Hle].
    apply le_lt_or_eq in Hle as [Hlt | ->]; [right | left]; last reflexivity.
    split; first (split; [ reflexivity | lia]).
    intros [_ Hle]. lia.
  Qed.

  Lemma evid_le_lt_trans: 
    ∀ t t' t'' : EvId,
      evid_le t t' → evid_lt t' t'' → evid_lt t t''.
  Proof. exact strict_transitive_r. Qed.

  Lemma evid_lt_le_trans: 
    ∀ t t' t'' : EvId,
      evid_lt t t' → evid_le t' t'' → evid_lt t t''.
  Proof. exact strict_transitive_l. Qed.

	Global Instance evid_lt_asym: Asymmetric evid_lt.
  Proof.
    intros[r s][r' s'] [[-> Hle] Hnle][[Heq Hle'] Hnle'].
    by apply Hnle.
	Qed.

  Global Instance eviq_time : Log_Time :=
    {| Time := EvId;
       TM_le := evid_le;
       TM_le_PO := evid_le_po;
       TM_lt := evid_lt;
       TM_lt_irreflexive := evid_lt_irreflexive;
       TM_lt_trans := evid_lt_trans;
       TM_le_eq_or_lt := evid_le_eq_or_lt;
       TM_lt_TM_le := evid_lt_TM_le;
       TM_le_lt_trans := evid_le_lt_trans;
       TM_lt_le_trans := evid_lt_le_trans
    |}.

End EVTime.

