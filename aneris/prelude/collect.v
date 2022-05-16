From Coq.ssr Require Import ssreflect.
From iris.algebra Require Import gmap gmultiset.

Section collect.
  Context {K} `{!EqDecision K} `{Countable K} {A : Type}
          {B : Type} `{!EqDecision B} `{Countable B}
          (f : K → A → gset B).

  Definition collect (g : gmap K A) : gset B :=
    map_fold (λ k a acc, (f k a) ∪ acc) ∅ g.

  Lemma collect_singleton k a :
    collect {[k := a]} = f k a.
  Proof.
    rewrite /collect.
    rewrite map_fold_insert_L.
    - simpl. rewrite map_fold_empty; set_solver.
    - set_solver.
    - done.
  Qed.

  Lemma collect_empty :
    collect ∅ = ∅.
  Proof. by rewrite /collect.
  Qed.

  Lemma collect_insert k a g :
    collect (<[k:=a]> g) = f k a ∪ collect (delete k g).
  Proof.
    generalize dependent a.
    generalize dependent k.
    pattern (collect g); pattern g.
    match goal with
    |- (λ x, (λ y, ?P) _) _ =>
      simpl; apply (map_fold_ind (M := gmap _) (B := gset B) (λ y, λ x, P))
    end; [ done | exact ∅ | |].
    - intros. rewrite collect_singleton; set_solver.
    - intros k' a' h acc Hk' IH k a.
      destruct (decide (k = k')) as [-> | Hneq].
      + rewrite insert_insert delete_insert_delete.
        set_solver.
      + rewrite delete_insert_ne; last done.
        assert ((<[k:=a]>(<[k':=a']> h)) = (<[k':=a']>(<[k:=a]> h))) as ->.
        { by rewrite insert_commute; last done. }
        rewrite /collect.
        rewrite {1} map_fold_insert_L.
        specialize (IH k a).
        rewrite /collect in IH.
        rewrite IH.
        rewrite {1} map_fold_insert_L.
        * set_solver.
        * set_solver.
        * by rewrite lookup_delete_ne.
        * set_solver.
        * by rewrite lookup_insert_ne; last done.
  Qed.


  Lemma collect_disjoint_union g h :
    g ##ₘ h →
    collect (g ∪ h) = collect g ∪ collect h.
  Proof.
    intros Hdisj.
    generalize dependent h.
    pattern (collect g); pattern g.
    match goal with
    |- (λ x, (λ y, ?P) _) _ =>
    simpl; apply (map_fold_ind (M := gmap _) (λ y, λ x, P))
    end.
    - intros. by rewrite !left_id_L.
    - intros k a g' acc Hk IHM h' Hdisj.
      assert (f k a ∪ acc ∪ collect h' =
              acc ∪ (f k a ∪ collect h')) as -> by set_solver.
      rewrite insert_union_singleton_l.
      assert ({[k := a]} ∪ g' ∪ h' =  g' ∪ ({[k := a]} ∪ h')) as ->.
      { rewrite (map_union_comm {[k := a]} g').
          by rewrite map_union_assoc.
          by apply map_disjoint_singleton_l_2. }
      rewrite IHM.
      + rewrite -insert_union_singleton_l.
        rewrite collect_insert.
        simplify_map_eq.
        rewrite delete_notin; last done.
        done.
      + apply map_disjoint_union_r_2.
        * by apply map_disjoint_singleton_r_2.
        * simplify_map_eq. set_solver.
  Qed.

  Lemma collect_empty_f g :
    (forall k a, g !! k = Some a → f k a = ∅) → collect g = ∅.
  Proof.
    pattern (collect g); pattern g.
    match goal with
    |- (λ x, (λ y, ?P) _) _ =>
      simpl; apply (map_fold_ind (M := gmap _) (λ y, λ x, P))
    end.
    - done.
    - intros k a g' M Hk IHM IHMi.
      rewrite empty_union_L; split.
      + specialize (IHMi k a). apply IHMi.
          by rewrite lookup_insert.
      + apply IHM. intros k' a' Hka'.
        specialize (IHMi k' a').
        apply IHMi.
        destruct (decide (k = k')) as [<-|Hneq]; by simplify_map_eq.
  Qed.

  Lemma elem_of_collect g :
    ∀ m, m ∈ collect g ↔ ∃ k a, g !! k = Some a ∧ m ∈ f k a.
  Proof.
    pattern (collect g); pattern g.
    match goal with
    |- (λ x, (λ y, ?P) _) _ =>
      simpl; apply (map_fold_ind (M := gmap _) (λ y, λ x, P))
    end.
    - intros m; split; first done.
      intros (?&?&?&?); done.
    - intros k a g' M Hk IHM m.
      split.
      + intros [Hm|Hm]%elem_of_union.
        * exists k, a; rewrite lookup_insert; done.
        * apply IHM in Hm as (k' & a' & Hk' & Hm).
          exists k', a'.
          rewrite lookup_insert_ne; first done.
          set_solver.
      + intros (k' & a' & Hk' & Hm).
        destruct (decide (k' = k)) as [->|].
        * rewrite lookup_insert in Hk'; simplify_eq.
          set_solver.
        * rewrite lookup_insert_ne in Hk'; last done.
          apply elem_of_union; right.
          apply IHM; eauto.
  Qed.

End collect.

Section multi_collect.
  Context {K} `{!EqDecision K} `{Countable K} {A : Type}
          {B : Type} `{!EqDecision B} `{Countable B}
          (f : K → A → gmultiset B).

  Definition multi_collect (g : gmap K A) : gmultiset B :=
    map_fold (λ k a acc, (f k a) ⊎ acc) ∅ g.

  Lemma multi_collect_singleton k a :
    multi_collect {[k := a]} = f k a.
  Proof.
    rewrite /multi_collect.
    rewrite map_fold_insert_L.
    - simpl. rewrite map_fold_empty; multiset_solver.
    - multiset_solver.
    - done.
  Qed.

  Lemma multi_collect_empty :
    multi_collect ∅ = ∅.
  Proof. by rewrite /multi_collect.
  Qed.

  Lemma multi_collect_insert k a g :
    multi_collect (<[k:=a]> g) = f k a ⊎ multi_collect (delete k g).
  Proof.
    generalize dependent a.
    generalize dependent k.
    pattern (multi_collect g); pattern g.
    match goal with
    |- (λ x, (λ y, ?P) _) _ =>
      simpl; apply (map_fold_ind (M := gmap _) (B := gset B) (λ y, λ x, P))
    end; [ done | exact ∅ | |].
    - intros. rewrite multi_collect_singleton; multiset_solver.
    - intros k' a' h acc Hk' IH k a.
      destruct (decide (k = k')) as [-> | Hneq].
      + rewrite insert_insert delete_insert_delete.
        set_solver.
      + rewrite delete_insert_ne; last done.
        assert ((<[k:=a]>(<[k':=a']> h)) = (<[k':=a']>(<[k:=a]> h))) as ->.
        { by rewrite insert_commute; last done. }
        rewrite /multi_collect.
        rewrite {1} map_fold_insert_L.
        specialize (IH k a).
        rewrite /multi_collect in IH.
        rewrite IH.
        rewrite {1} map_fold_insert_L.
        * multiset_solver.
        * multiset_solver.
        * by rewrite lookup_delete_ne.
        * multiset_solver.
        * by rewrite lookup_insert_ne; last done.
  Qed.


  Lemma multi_collect_disjoint_union g h :
    g ##ₘ h →
    multi_collect (g ∪ h) = multi_collect g ⊎ multi_collect h.
  Proof.
    intros Hdisj.
    generalize dependent h.
    pattern (multi_collect g); pattern g.
    match goal with
    |- (λ x, (λ y, ?P) _) _ =>
    simpl; apply (map_fold_ind (M := gmap _) (λ y, λ x, P))
    end.
    - intros. by rewrite !left_id_L.
    - intros k a g' acc Hk IHM h' Hdisj.
      assert (f k a ⊎ acc ⊎ multi_collect h' =
              acc ⊎ (f k a ⊎ multi_collect h')) as -> by multiset_solver.
      rewrite insert_union_singleton_l.
      assert ({[k := a]} ∪ g' ∪ h' =  g' ∪ ({[k := a]} ∪ h')) as ->.
      { rewrite (map_union_comm {[k := a]} g').
          by rewrite map_union_assoc.
          by apply map_disjoint_singleton_l_2. }
      rewrite IHM.
      + rewrite -insert_union_singleton_l.
        rewrite multi_collect_insert.
        simplify_map_eq.
        rewrite delete_notin; last done.
        done.
      + apply map_disjoint_union_r_2.
        * by apply map_disjoint_singleton_r_2.
        * simplify_map_eq. set_solver.
  Qed.

  Lemma multi_collect_empty_f g :
    (forall k a, g !! k = Some a → f k a = ∅) → multi_collect g = ∅.
  Proof.
    pattern (multi_collect g); pattern g.
    match goal with
    |- (λ x, (λ y, ?P) _) _ =>
      simpl; apply (map_fold_ind (M := gmap _) (λ y, λ x, P))
    end.
    - done.
    - intros k a g' M Hk IHM IHMi.
      cut (f k a = ∅ ∧ M = ∅). (* TODO: add to stdpp *)
      { multiset_solver. }
      split.
      + specialize (IHMi k a). apply IHMi.
          by rewrite lookup_insert.
      + apply IHM. intros k' a' Hka'.
        specialize (IHMi k' a').
        apply IHMi.
        destruct (decide (k = k')) as [<-|Hneq]; by simplify_map_eq.
  Qed.

  Lemma elem_of_multi_collect g :
    ∀ m, m ∈ multi_collect g ↔ ∃ k a, g !! k = Some a ∧ m ∈ f k a.
  Proof.
    pattern (multi_collect g); pattern g.
    match goal with
    |- (λ x, (λ y, ?P) _) _ =>
      simpl; apply (map_fold_ind (M := gmap _) (λ y, λ x, P))
    end.
    - intros m; split; first multiset_solver.
      intros (?&?&?&?); done.
    - intros k a g' M Hk IHM m.
      split.
      + intros [Hm|Hm]%gmultiset_elem_of_disj_union.
        * exists k, a; rewrite lookup_insert; done.
        * apply IHM in Hm as (k' & a' & Hk' & Hm).
          exists k', a'.
          rewrite lookup_insert_ne; first done.
          set_solver.
      + intros (k' & a' & Hk' & Hm).
        destruct (decide (k' = k)) as [->|].
        * rewrite lookup_insert in Hk'; simplify_eq.
          set_solver.
        * rewrite lookup_insert_ne in Hk'; last done.
          apply gmultiset_elem_of_disj_union; right.
          apply IHM; eauto.
  Qed.

  Lemma multi_collect_subseteq (g1 g2 : gmap K A) :
    (∀ k v1, g1 !! k = Some v1 -> ∃ v2, g2 !! k = Some v2 ∧ f k v1 ⊆ f k v2) ->
    multi_collect g1 ⊆ multi_collect g2.
  Proof.
    generalize dependent g2. pattern (multi_collect g1); pattern g1.
    match goal with
    |- (λ x, (λ y, ?P) _) _ =>
      simpl; apply (map_fold_ind (M := gmap _) (λ y, λ x, P))
    end.
    - intros g2 Hf. multiset_solver.
    - intros i a m r Hnone IH g2 Hf'. rewrite /multi_collect.
      pose proof (Hf' i a) as Hin.
      rewrite lookup_insert in Hin.
      destruct (Hin eq_refl) as (a' & Hing2 & Hfincl).
      rewrite -(insert_delete g2 i a') //.
      rewrite map_fold_insert_L //; last first.
      { rewrite lookup_delete //. }
      { intros. multiset_solver. }
      assert (r ⊆ map_fold (λ (k : K) (a0 : A) (acc : gmultiset B), f k a0 ⊎ acc) ∅ (delete i g2));
        last multiset_solver.
      apply IH. intros k v Hv. destruct (decide (i = k)) as [<-|Hneq]; first congruence.
      rewrite lookup_delete_ne //. apply Hf'. rewrite lookup_insert_ne //.
  Qed.
End multi_collect.
