From stdpp Require Export sets gmap mapset.
From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates big_op.

Record disj_gsets K `{Countable K} := DGSets { dgsets_of : (gset (gset K)) }.
Global Arguments dgsets_of {_ _ _} _.
Global Arguments DGSets {_ _ _} _.

Definition eq_or_disj `{Countable K} (X Y : gset K) : Prop :=
  X = Y ∨ X ## Y.

Lemma eq_or_disj_comm `{Countable K} (x y : gset K) :
  eq_or_disj x y → eq_or_disj y x.
Proof. rewrite /eq_or_disj. intros [Hdisj | Hidjs]; eauto. Qed.

Lemma eq_or_disj_singleton `{Countable K} (x y : K) :
  eq_or_disj {[x]} {[y]}.
Proof. rewrite /eq_or_disj. destruct (decide (x = y)); set_solver. Qed.

Section disj_gsets.
  Context `{Countable K}.
  Local Arguments op _ _ !_ !_ /.
  Local Arguments cmra_op _ !_ !_ /.
  Local Arguments ucmra_op _ !_ !_ /.

  Canonical Structure disj_gsetsO := leibnizO (disj_gsets K).

  Definition have_disj_elems (X Y : gset (gset K)) : Prop :=
    ∀ x y, x ∈ X → y ∈ Y → eq_or_disj x y.

  Definition all_disjoint (X : gset (gset K)) : Prop := have_disj_elems X X.

  Local Instance disj_gsets_valid_instance : Valid (disj_gsets K) :=
    λ X, all_disjoint (dgsets_of X).
  Local Instance disj_gsets_unit_instance : Unit (disj_gsets K) := DGSets ∅.
  Local Instance disj_gsets_op_instance : Op (disj_gsets K) :=
    λ X Y, DGSets (dgsets_of X ∪ dgsets_of Y).
  Local Instance disj_gsets_pcore_instance : PCore (disj_gsets K) := λ x, Some x.

  Lemma have_disj_elems_comm X Y : have_disj_elems X Y → have_disj_elems Y X.
  Proof. intros HXY x y ??; destruct (HXY y x); rewrite /eq_or_disj; auto. Qed.

  Lemma all_disjoint_union X Y :
    (all_disjoint X ∧ all_disjoint Y ∧ have_disj_elems X Y) ↔ all_disjoint (X ∪ Y).
  Proof.
    split.
    - intros (HX & HY & HXY) x y [Hx|Hx]%elem_of_union [Hy|Hy]%elem_of_union.
      + by apply HX.
      + by apply HXY.
      + apply have_disj_elems_comm in HXY. by apply HXY.
      + by apply HY.
    - intros HXY; split_and!.
      + intros ????; apply HXY; set_solver.
      + intros ????; apply HXY; set_solver.
      + intros ????; apply HXY; set_solver.
  Qed.

  Lemma have_disj_elems_subseteq X Y X' Y' :
    X ⊆ X' → Y ⊆ Y' → have_disj_elems X' Y' → have_disj_elems X Y.
  Proof. intros ?? HX'Y' ????; apply HX'Y'; set_solver. Qed.

  Lemma have_disj_elems_singleton z X :
    (∀ x, x ∈ X → z = x ∨ z ## x) ↔ have_disj_elems {[z]} X.
  Proof.
    split.
    - intros Hz ? y ->%elem_of_singleton ?; apply Hz; done.
    - intros HX x Hx; apply HX; set_solver.
  Qed.

  Lemma have_disj_elems_union X Y Z :
    have_disj_elems X Y →
    have_disj_elems X Z →
    have_disj_elems X (Y ∪ Z).
  Proof.
    intros Hdisj1 Hdisj2.
    intros y1 y2 Hin1 Hin2%elem_of_union.
    destruct Hin2 as [Hin2|Hin2].
    - by apply Hdisj1.
    - by apply Hdisj2.
  Qed.

  Lemma have_disj_elems_union_2 X Y Z :
    all_disjoint Z →
    have_disj_elems X Z →
    have_disj_elems Y Z →
    have_disj_elems X Y →
    have_disj_elems (X ∪ Z) (Y ∪ Z).
  Proof.
    intros Hdisj HdisjXZ HdisjYZ HdisjXY.
    apply have_disj_elems_union.
    - apply have_disj_elems_comm.
      apply have_disj_elems_union;
        [ apply have_disj_elems_comm, HdisjXY | apply HdisjYZ ].
    - apply have_disj_elems_comm.
      apply have_disj_elems_union;
        [ apply have_disj_elems_comm, HdisjXZ | apply Hdisj ].
  Qed.

  Lemma all_disjoint_subseteq X X' : X ⊆ X' → all_disjoint X' → all_disjoint X.
  Proof. intros ? ?; eapply have_disj_elems_subseteq; eauto. Qed.

  Lemma all_disjoint_singleton z : all_disjoint {[z]}.
  Proof. apply have_disj_elems_singleton; set_solver. Qed.

  Lemma elem_of_all_disjoint_eq x1 x2 x (X : gset (gset K)) :
    all_disjoint X → x1 ∈ X → x2 ∈ X → x ∈ x1 → x ∈ x2 → x1 = x2.
  Proof.
    intros Hdisj Hin1 Hin2 Hxin1 Hxin2.
    destruct (Hdisj x1 x2 Hin1 Hin2) as [->|Hdisj']; [done|].
    by specialize (Hdisj' x Hxin1 Hxin2).
  Qed.

  Lemma elem_of_all_disjoint_neq x1 x2 x (X : gset (gset K)) :
    all_disjoint X → x1 ∈ X → x2 ∈ X → x ∈ x1 → x ∉ x2 → x1 ## x2.
  Proof.
    intros Hdisj Hin1 Hin2 Hxin1 Hxin2.
    destruct (Hdisj x1 x2 Hin1 Hin2) as [->|Hdisj']; [done|done].
  Qed.

  Lemma disjoint_empty_ne (X Y : gset K) :
    X ## Y → X ≠ ∅ → Y ≠ ∅ → X ≠ Y.
  Proof. intros Hdisj HX HY. set_solver. Qed.

  Lemma have_disj_elems_both_singletons x y : have_disj_elems {[x]} {[y]} ↔ x = y ∨ x ## y.
  Proof. rewrite -have_disj_elems_singleton; set_solver. Qed.

  Lemma have_disj_elems_empty X : have_disj_elems ∅ X.
  Proof. intros ? y ?%elem_of_empty; done. Qed.

  Lemma all_disjoint_empty : all_disjoint ∅.
  Proof. apply have_disj_elems_empty. Qed.

  Lemma disj_gsets_included X Y : DGSets X ≼ DGSets Y ↔ X ⊆ Y.
  Proof.
    split.
    - move=> [[Z]]; rewrite /= /disj_gsets_op_instance /=; set_solver.
    - intros (Z&->&?)%subseteq_disjoint_union_L.
      exists (DGSets Z); done.
  Qed.
  Lemma disj_gsets_valid (X : gset (gset K)) :
    ✓ (DGSets X) ↔ all_disjoint X.
  Proof. done. Qed.
  Lemma disj_gsets_valid_op X Y :
    ✓ (DGSets X ⋅ DGSets Y) ↔ all_disjoint X ∧ all_disjoint Y ∧ have_disj_elems X Y.
  Proof. rewrite all_disjoint_union; done. Qed.
  Lemma disj_gsets_valid_op_singletons_disjoint x y :
    ✓ (DGSets {[x]} ⋅ DGSets {[y]}) ↔ x = y ∨ x ## y.
  Proof.
    rewrite disj_gsets_valid_op have_disj_elems_both_singletons.
    split; [tauto|by auto using all_disjoint_singleton].
  Qed.
  Lemma disj_gsets_op_union X Y : DGSets X ⋅ DGSets Y = DGSets (X ∪ Y).
  Proof. done. Qed.

  Lemma disj_gsets_ra_mixin : RAMixin (disj_gsets K).
  Proof.
    apply ra_total_mixin.
    - eauto.
    - intros [X] [] [] ?%leibniz_equiv; simplify_eq; done.
    - intros ?? ->%leibniz_equiv; done.
    - intros ?? ->%leibniz_equiv; done.
    - intros [] [] []; rewrite /= /disj_gsets_op_instance /= assoc_L; done.
    - intros [] []; rewrite /= /disj_gsets_op_instance /= comm_L; done.
    - intros []; rewrite /= /disj_gsets_op_instance /= union_idemp_L; done.
    - done.
    - done.
    - intros [] []; rewrite disj_gsets_valid_op; intros (?&?&?); done.
  Qed.
  Canonical Structure disj_gsetsR := discreteR (disj_gsets K) disj_gsets_ra_mixin.

  Global Instance disj_gsets_cmra_discrete : CmraDiscrete disj_gsetsR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance disj_gsets_core_id X : CoreId (DGSets X).
  Proof. by constructor. Qed.

  Lemma disj_gsets_ucmra_mixin : UcmraMixin (disj_gsets K).
  Proof.
    split; [done| |done].
    intros [X]; rewrite /= /disj_gsets_op_instance /=; f_equiv; set_solver.
  Qed.
  Canonical Structure disj_gsetsUR := Ucmra (disj_gsets K) disj_gsets_ucmra_mixin.

  Local Arguments op _ _ _ _ : simpl never.

  Lemma disj_gsets_alloc_op_local_update X Y Z :
    all_disjoint Z →
    have_disj_elems Z X →
    (DGSets X, DGSets Y) ~l~> (DGSets Z ⋅ DGSets X, DGSets Z ⋅ DGSets Y).
  Proof. intros; apply op_local_update_discrete; rewrite disj_gsets_valid_op; done. Qed.
  Lemma disj_gsets_alloc_union_local_update X Y Z :
    all_disjoint Z →
    have_disj_elems Z X →
    (DGSets X, DGSets Y) ~l~> (DGSets (Z ∪ X), DGSets (Z ∪ Y)).
  Proof. apply disj_gsets_alloc_op_local_update. Qed.

  Lemma disj_gset_alloc_empty_local_update X Z :
    all_disjoint Z →
    have_disj_elems Z X →
    (DGSets X, DGSets ∅) ~l~> (DGSets (Z ∪ X), DGSets Z).
  Proof.
    intros. rewrite -{2}(right_id_L _ union Z).
    apply disj_gsets_alloc_union_local_update; done.
  Qed.
End disj_gsets.

Global Arguments disj_gsetsO _ {_ _}.
Global Arguments disj_gsetsR _ {_ _}.
Global Arguments disj_gsetsUR _ {_ _}.
