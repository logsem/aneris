From stdpp Require Import gmap.
From aneris.examples.crdt.spec Require Import crdt_time.

Section Defs.

  Definition RepId := nat.
  Definition SeqNum := nat.
  Definition EvId : Type := RepId * SeqNum.
  Definition Timestamp : Type := gset EvId.


  Definition evid_le (ts1 ts2 : EvId) : Prop.
  Proof.
    destruct ts1 as [rid sid]; destruct ts2 as [rid' sid'].
    exact (rid = rid' ∧ (sid ≤ sid')%nat).
  Defined.

	Global Instance evid_le_refl: Reflexive evid_le.
  Proof. by intros[]. Qed.

  Global Instance evid_le_trans : Transitive evid_le.
  Proof.
    intros [r s][r' s'][r'' s''][-> Hle][<- Hle'].
    split; [ reflexivity | by apply le_trans with s'].
  Qed.

  Global Instance evid_le_antisym: AntiSymm eq evid_le.
  Proof.
    intros[r s][r' s'] [-> Hle] [Heq Hle'].
    apply pair_equal_spec; split; [reflexivity | by apply le_antisym].
  Qed.

	Global Instance evid_le_po: PartialOrder evid_le.
  Proof. repeat split;  exact _. Qed.



  Definition evid_lt := strict evid_le.

End Defs.

Section TODOMove.

  Definition frac_gt_half : Qp := 2/3.
  Definition frac_gt_half_diff : Qp := 1/3.

End TODOMove.
