From Coq.ssr Require Export ssreflect.
From stdpp Require Import base vector list_numbers.
From aneris.prelude Require Import list.


Notation vector_clock n := (vec nat n).

Definition vc_merge {n : nat} (v1 v2 : vector_clock n) : vector_clock n :=
  vzip_with max v1 v2.

Definition vc_le {n : nat} (v1 v2 : vector_clock n) : Prop :=
  ∀ i, le (v1 !!! i) (v2 !!! i).

Definition vc_incr {n : nat} (i : fin n) (v : vector_clock n) : vector_clock n :=
  vinsert i (S (v !!! i)) v.

Global Instance vc_le_PO n : PartialOrder (@vc_le n).
Proof.
  split; first split.
  - intros vc i; done.
  - intros vc1 vc2 vc3 Hvc12 Hvc23 i.
    etrans; eauto.
  - intros vc1 vc2 Hvc12 Hvc21.
    apply vec_eq; intros i.
    apply Nat.le_antisymm; done.
Qed.

Lemma vc_le_antisymm n (vc1 vc2 : vector_clock n) : vc_le vc1 vc2 → vc_le vc2 vc1 → vc1 = vc2.
Proof. apply anti_symm; apply _. Qed.

Lemma vc_merge_le1 n (vc1 vc2 : vector_clock n) : vc_le vc1 (vc_merge vc1 vc2).
Proof. intros i; rewrite /vc_merge vlookup_zip_with; lia. Qed.

Lemma vc_merge_le2 n (vc1 vc2 : vector_clock n) : vc_le vc2 (vc_merge vc1 vc2).
Proof. intros i; rewrite /vc_merge vlookup_zip_with; lia. Qed.

Lemma vc_merge_lub n (vc1 vc2 vc3 : vector_clock n) :
  vc_le vc1 vc3 → vc_le vc2 vc3 → vc_le (vc_merge vc1 vc2) vc3.
Proof.
  intros Hvc13 Hvc23 i; rewrite /vc_merge vlookup_zip_with.
  apply Nat.max_lub; done.
Qed.

Lemma vc_merge_vc_le n (vc vc' : vector_clock n) : vc_le vc vc' → vc_merge vc vc' = vc'.
Proof.
  intros Hvcs.
  apply vc_le_antisymm.
  - apply vc_merge_lub; done.
  - apply vc_merge_le2.
Qed.

Global Instance vc_merge_comm n : Comm eq (@vc_merge n).
Proof. intros ??; apply vec_eq; intros ?; rewrite /vc_merge !vlookup_zip_with; lia. Qed.

Lemma vc_incr_le n i (vc : vector_clock n) : vc_le vc (vc_incr i vc).
Proof.
  intros j; rewrite /vc_incr.
  destruct (decide (i = j)) as [->|].
  - rewrite vlookup_insert; lia.
  - rewrite vlookup_insert_ne //.
Qed.

Definition max_vc {n m} (s : vec (vector_clock n) m) : vector_clock n :=
  Vector.fold_right vc_merge s (vreplicate n 0).

Lemma max_vc_le n m (s : vec (vector_clock n) m) i : vc_le (s !!! i) (max_vc s).
Proof.
  induction s as [|vc m s IHs]; first by inversion i.
  rewrite /max_vc /=.
  inv_all_vec_fin; simpl.
  - apply vc_merge_le1.
  - etrans; first by apply IHs.
    apply vc_merge_le2.
Qed.

Lemma max_vc_ub n m (s : vec (vector_clock n) m) vc :
  (∀ i, vc_le (s !!! i) vc) → vc_le (max_vc s) vc.
Proof.
  induction s as [|vc' m s IHs].
  { intros _. intros ?; rewrite /max_vc /= vlookup_replicate; lia. }
  intros Hvc.
  rewrite /max_vc /=.
  apply vc_merge_lub.
  - specialize (Hvc 0%fin); done.
  - apply IHs; intros i.
    specialize (Hvc (Fin.FS i)); done.
Qed.

Lemma vc_le_cons n a b (v v' : vector_clock n) :
  vc_le (a ::: v) (b ::: v') ↔ a ≤ b ∧ vc_le v v'.
Proof.
  split.
  - intros Hle; split.
    + specialize (Hle 0%fin); done.
    + intros i. specialize (Hle (Fin.FS i)); done.
  - intros [Hab Hle] i.
    inv_all_vec_fin; first done.
    apply Hle.
Qed.

Fixpoint all_vecs_smaller {n} (v : vector_clock n) : list (vector_clock n) :=
  match v with
  | [#] => [[#]]
  | n ::: l' => flatten ((λ m, (λ k, m ::: k) <$> (all_vecs_smaller l')) <$> (seq 0 (S n)))
  end.

Lemma elem_of_all_vecs_smaller_cons n a (v : vector_clock n) (v' : vector_clock (S n)) :
  v' ∈ all_vecs_smaller (a ::: v) ↔ ∃ b v'', v' = b ::: v'' ∧ b ≤ a ∧ v'' ∈ all_vecs_smaller v.
Proof.
  cbn [all_vecs_smaller].
  rewrite elem_of_flatten.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_seq.
  split.
  - intros (l'' & Hl' & b & -> & Hl'').
    apply elem_of_list_fmap in Hl' as (l2 & -> & Hl2).
    eexists _, _; split_and!; [done|lia|done].
  - intros (b & v'' & -> & Hb & Hv'').
    eexists _; split; [|exists b; split; [reflexivity|lia]].
    apply elem_of_list_fmap; eauto.
Qed.

Lemma make_vc {A} k (l : list A) : length l = k → {v : vec A k | vec_to_list v = l}.
Proof.
  intros Hlen.
  refine (match Hlen in _ = z return {v : vec A z | vec_to_list v = l } with
          | eq_refl => _
          end).
  exists (list_to_vec l); rewrite vec_to_list_to_vec; done.
Qed.

Lemma elem_of_all_vecs_smaller n (v' v : vector_clock n) :
  v' ∈ all_vecs_smaller v ↔ vc_le v' v.
Proof.
  revert v'; induction v as [|a m v IHv]; simpl; intros v'.
  { split.
    - intros ->%elem_of_list_singleton; done.
    - intros ?.
      apply (Vector.case0 (λ v', v' ∈ [[# ]])).
      apply elem_of_list_singleton; done. }
  rewrite elem_of_all_vecs_smaller_cons.
  split.
  - intros (b & v'' & -> & Hb & Hv''); simpl.
    apply vc_le_cons; split; first done.
    apply IHv; done.
  - inv_all_vec_fin.
    intros [? ?]%vc_le_cons.
    eexists _, _; split; first done.
    split; first done.
    apply IHv; done.
Qed.
