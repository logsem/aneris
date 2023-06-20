From stdpp Require Import gmap fin_maps.
Require Import ssreflect.
From aneris.prelude Require Import gset_map.
From aneris.algebra Require Import disj_gsets.
From iris.algebra Require Import auth.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Import weakestpre adequacy.

Definition is_singleton `{Countable K} (X : gset K) : Prop :=
  ∃ x, X = {[x]}.

Definition is_ne `{Countable K} (X : gset K) : Prop :=
  X ≠ ∅.

Definition to_singletons `{Countable K} (X : gset K) : gset (gset K) :=
  gset_map (λ x, {[x]}) X.

#[global] Instance to_singletons_injective `{Countable K} :
  Inj (=) (=) (@to_singletons K _ _).
Proof. apply _. Qed.

Definition union_set `{Countable A} `{Empty A} `{Union A} (s : gset A) : A :=
  union_list (elements s).
Notation "⋃ₛ s" := (union_set s) (at level 20, format "⋃ₛ  s") : stdpp_scope.

Section with_K.
  Context `{Countable K}.

  Lemma to_singletons_union (X Y : gset K) :
    to_singletons (X ∪ Y) = to_singletons X ∪ to_singletons Y.
  Proof. set_solver. Qed.

  Lemma to_singletons_fmap (f : gset K → Prop) (X : gset K) :
    (∀ (x : K), f {[x]}) → set_Forall f (to_singletons X).
  Proof.
    intros Hf.
    induction X as [|x X Hin IHX] using set_ind_L.
    { done. }
    rewrite /to_singletons.
    rewrite gset_map_union.
    eapply set_Forall_union.
    { rewrite gset_map_singleton.
      apply set_Forall_singleton.
      rewrite /is_singleton.
      apply Hf. }
    done.
  Qed.

  Lemma to_singletons_all_singleton (X : gset K) :
    set_Forall is_singleton (to_singletons X).
  Proof. apply to_singletons_fmap. intros x. rewrite /is_singleton. set_solver. Qed.

  Lemma all_is_singleton_all_disjoint (X : gset (gset K)) :
    set_Forall is_singleton X → all_disjoint X.
  Proof.
    intros Hsingle.
    induction X as [|x X HninX IHX] using set_ind_L.
    { done. }
    epose proof (set_Forall_union_inv_1 _ {[x]} X Hsingle) as Hsinglex.
    epose proof (set_Forall_union_inv_2 _ {[x]} X Hsingle) as HsingleX.
    setoid_rewrite <-all_disjoint_union.
    split; [ apply all_disjoint_singleton | ].
    split; [by apply IHX|].
    apply have_disj_elems_singleton.
    setoid_rewrite set_Forall_singleton in Hsinglex.
    intros x' Hx'.
    destruct (decide (x = x')).
    { by left. }
    right.
    destruct Hsinglex as [y ->].
    assert (∃ y', x' = {[y']}) as [y' ->].
    { by apply HsingleX. }
    set_solver.
  Qed.

  Lemma to_singletons_all_disjoint (X : gset K) :
    all_disjoint (to_singletons X).
  Proof. apply all_is_singleton_all_disjoint. apply to_singletons_all_singleton. Qed.

  Lemma to_singletons_is_ne (X : gset K) :
    set_Forall is_ne (to_singletons X).
  Proof.
    apply to_singletons_fmap.
    intros x. rewrite /is_ne. set_solver.
  Qed.

  Lemma gset_map_difference_comm `{Countable U} (f : K → U)
        `{Inj _ _ (=) (=) f} (X Y : gset K) :
    (gset_map f X) ∖ (gset_map f Y) = gset_map f (X ∖ Y).
  Proof.
    apply set_eq.
    intros x.
    split; intros Hin.
    - assert (x ∈ gset_map f X) as HX by set_solver.
      apply (gset_map_correct2) in HX as [a [Heq HX]].
      rewrite Heq.
      apply gset_map_correct1. set_solver.
    - apply (gset_map_correct2) in Hin as [a [Heq HX]].
      simplify_eq.
      set_solver.
  Qed.


  Lemma to_singletons_difference_comm (X Y : gset K) :
    (to_singletons X) ∖ (to_singletons Y) = to_singletons (X ∖ Y).
  Proof. apply gset_map_difference_comm. apply _. Qed.

  Lemma big_sepS_fmap `{invGS_gen hlc Σ} `{Countable K} `{Countable U}
        (f : K → U) `{Inj _ _ (=) (=) f} (X : gset K)
        (Φ : U → iProp Σ) (Ψ : K → iProp Σ) :
    □ (∀ x, Φ (f x) -∗ Ψ x) -∗
      ([∗ set] x ∈ gset_map f X, Φ x) -∗ ([∗ set] x ∈ X, Ψ x).
  Proof.
    iIntros "#Hf HX".
    rewrite big_op.big_opS_unseal /big_op.big_opS_def.
    rewrite -elements_fmap.
    rewrite big_sepL_fmap.
    iApply (big_sepL_impl with "HX").
    iIntros "!>" (k x Hin) "HΦ".
      by iApply "Hf".
  Qed.

  Lemma big_sepS_to_singletons `{invGS_gen hlc Σ} `{Countable K}
        (X : gset K) (Φ : gset K → iProp Σ) (Ψ : K → iProp Σ) :
    □ (∀ x, Φ {[x]} -∗ Ψ x) -∗
      ([∗ set] x ∈ to_singletons X, Φ x) -∗ ([∗ set] x ∈ X, Ψ x).
  Proof. apply big_sepS_fmap. apply _. Qed.

  Lemma to_singletons_inv (x : K) :
    to_singletons {[x]} = {[{[x]}]}.
  Proof. rewrite /to_singletons. by rewrite gset_map_singleton. Qed.

  Lemma elem_of_to_singletons
        (X : gset K) x :
    x ∈ X ↔ {[x]} ∈ to_singletons X.
  Proof.
    split; intros Hx.
    - assert ({[x]} ∪ X = X) as <- by set_solver.
      rewrite to_singletons_union.
      set_solver.
    - induction X using set_ind_L.
      { done. }
      rewrite to_singletons_union in Hx.
      apply elem_of_union in Hx.
      destruct Hx as [Hx | Hx].
      + rewrite to_singletons_inv in Hx. set_solver.
      + apply IHX in Hx. set_solver.
  Qed.

  Lemma elem_of_to_singletons_inv (X : gset K) x :
    x ∈ to_singletons X → is_singleton x.
  Proof. intros Hx. by eapply to_singletons_all_singleton. Qed.

  Lemma elem_of_union_set x (Xs : gset (gset K)) :
    x ∈ ⋃ₛ Xs ↔ (∃ X : gset K, X ∈ Xs ∧ x ∈ X).
  Proof.
    rewrite /union_set.
    rewrite elem_of_union_list.
    split.
    - intros HXs.
      destruct HXs as [X [Hxs Hx]].
      exists X. split; [|done].
      by apply elem_of_elements.
    - intros HXs.
      destruct HXs as [X [Hxs Hx]].
      exists X. split; [|done].
      by apply elem_of_elements.
  Qed.

  Lemma elem_of_union_set_mono (Xs : gset (gset K)) X x :
    X ∈ Xs → x ∈ X → x ∈ ⋃ₛ Xs.
  Proof. intros HXs HX. apply elem_of_union_list. set_solver. Qed.

  Lemma not_elem_of_union_set (Xs : gset (gset K)) x :
    x ∉ ⋃ₛ Xs → ∀ X, x ∈ X → X ∉ Xs.
  Proof.
    intros Hnin X Hin Hin'.
    apply Hnin.
    rewrite elem_of_union_list.
    eexists X.
    split; set_solver.
  Qed.

  Lemma not_elem_of_union_set_singleton (Xs : gset (gset K)) x :
    x ∉ ⋃ₛ Xs → {[x]} ∉ Xs.
  Proof. intros Hnin. eapply not_elem_of_union_set; [done|set_solver]. Qed.

  Lemma all_disjoint_have_disj_elems_singleton (Xs : gset (gset K)) x :
    all_disjoint Xs → x ∉ ⋃ₛ Xs → have_disj_elems {[{[x]}]} Xs.
  Proof.
    intros Hdisj Hnin.
    pose proof (not_elem_of_union_set _ _ Hnin).
    apply have_disj_elems_singleton.
    set_solver.
  Qed.

  Lemma have_disj_elems_elem_of (Xs : gset (gset K)) X :
    X ∈ Xs → all_disjoint Xs → have_disj_elems {[X]} Xs.
  Proof.
    intros Hin Hdisj.
    apply all_disjoint_union.
    assert ({[X]} ∪ Xs = Xs) as -> by set_solver.
    done.
  Qed.

  Lemma not_elem_of_union_set_difference x (Xs Ys : gset (gset K)) :
    x ∉ ⋃ₛ Ys → x ∉ ⋃ₛ (Xs ∖ Ys) → x ∉ ⋃ₛ Xs.
  Proof.
    intros HY HXY.
    setoid_rewrite elem_of_union_set in HY.
    setoid_rewrite elem_of_union_set in HXY.
    rewrite elem_of_union_set.
    intros HX.
    destruct HX as [X' [HX HX']].
    apply HXY.
    exists X'.
    split; [|done].
    apply elem_of_difference.
    split; [done|].
    intros HXY'.
    apply HY.
    exists X'.
    done.
  Qed.

  Lemma elem_of_union_set_singletons x (Xs : gset (gset K)) :
    set_Forall is_singleton Xs →
    x ∈ ⋃ₛ Xs → {[x]} ∈ Xs.
  Proof.
    intros Hsingle Hin.
    apply elem_of_union_set in Hin.
    destruct Hin as [X' [HX HX']].
    specialize (Hsingle X' HX).
    destruct Hsingle as [y Hy].
    destruct (decide (x = y)).
    { set_solver. }
    subst.
    assert (x = y) by set_solver.
    done.
  Qed.

  Lemma not_elem_of_to_singletons_union_set x (Xs : gset K) :
    x ∉ Xs → x ∉ ⋃ₛ to_singletons Xs.
  Proof.
    intros Hnin.
    rewrite elem_of_union_set.
    intros [X [Hin Hin']].
    pose proof (elem_of_to_singletons_inv Xs X Hin) as Hsingle.
    destruct Hsingle as [x' Hx]; subst.
    setoid_rewrite <-elem_of_to_singletons in Hin.
    set_solver.
  Qed.

  Lemma union_set_empty :
    ⋃ₛ (∅:gset $ gset K) = ∅.
  Proof. done. Qed.

  Lemma union_set_singleton (a : gset K) :
    ⋃ₛ {[a]} = a.
  Proof.
    rewrite /union_set. rewrite elements_singleton.
    simpl. rewrite right_id_L. done.
  Qed.

  Lemma union_set_union (A B : gset $ gset K) :
    A ## B → ⋃ₛ (A ∪ B) = (⋃ₛ A) ∪ (⋃ₛ B).
  Proof.
    intros Hdisj. rewrite /union_set.
    rewrite elements_disj_union; [|set_solver].
    rewrite union_list_app_L. done.
  Qed.

  Lemma to_singletons_singleton (a : K) :
    to_singletons {[a]} = {[{[a]}]}.
  Proof. rewrite /to_singletons. by rewrite gset_map.gset_map_singleton. Qed.

  (* OBS: This can be made stronger *)
  Lemma to_singletons_disj (A B : gset K) :
    A ## B → to_singletons A ## to_singletons B.
  Proof. rewrite /to_singletons. apply gset_map.gset_map_disj_union. apply _. Qed.

  Lemma union_set_to_singletons (A : gset K) :
    ⋃ₛ to_singletons A = A.
  Proof.
    induction A using set_ind_L; [done|].
    rewrite to_singletons_union.
    rewrite union_set_union; last first.
    { apply to_singletons_disj. set_solver. }
    rewrite IHA. f_equiv.
    rewrite to_singletons_singleton. by rewrite union_set_singleton.
  Qed.

End with_K.
