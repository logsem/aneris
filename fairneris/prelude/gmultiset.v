From stdpp Require Import gmultiset gmap.
From Coq.ssr Require Import ssreflect.


Section lemmas.
  Context `{!EqDecision A} `{!Countable A}.

  Implicit Types M N : gmultiset A.
  Implicit Types X Y : gset A.
  Implicit Types x y : A.

  Definition gset_of_gmultiset (M : gmultiset A) : gset A := dom M.

  Lemma elem_of_gset_of_gmultiset M x : x ∈ gset_of_gmultiset M ↔ (0 < multiplicity x M).
  Proof. rewrite /gset_of_gmultiset gmultiset_elem_of_dom. apply elem_of_multiplicity. Qed.

  Lemma gset_of_gmultiset_empty : gset_of_gmultiset ∅ = ∅.
  Proof. eapply @dom_empty_L; apply _. Qed.

  Lemma gset_of_gmultiset_singleton x : gset_of_gmultiset {[+ x +]} = {[ x ]}.
  Proof. apply dom_singleton_L. Qed.

  Lemma gmultiset_difference_subseteq M N : M ∖ N ⊆ M.
  Proof. intros x; rewrite multiplicity_difference; lia. Qed.

  Lemma gmultiset_difference_after_disj_union M N : (M ⊎ N) ∖ N = M.
  Proof.
    apply gmultiset_eq; intros x.
    rewrite multiplicity_difference multiplicity_disj_union.
    lia.
  Qed.

  Lemma gset_of_gmultiset_disj_union M N :
    gset_of_gmultiset (M ⊎ N) = (gset_of_gmultiset M) ∪ (gset_of_gmultiset N).
  Proof.
    apply set_eq=> x.
    rewrite elem_of_union !elem_of_gset_of_gmultiset multiplicity_disj_union.
    lia.
  Qed.

  Lemma gset_of_gmultiset_subseteq_mono M N :
    N ⊆ M → gset_of_gmultiset N ⊆ gset_of_gmultiset M.
  Proof.
    intros Hle x. rewrite !elem_of_gset_of_gmultiset.
    intros Hin. specialize (Hle x). lia.
  Qed.

  Lemma gset_of_gmultiset_disj_union_subseteq M N :
    N ⊆ M → gset_of_gmultiset (M ⊎ N) = gset_of_gmultiset M.
  Proof.
    intros Hle. rewrite gset_of_gmultiset_disj_union.
    apply gset_of_gmultiset_subseteq_mono in Hle. set_solver.
  Qed.

End lemmas.
