From iris.algebra Require Import gmap.

Lemma nat_Z_eq (n : nat) (z : Z) :
  (0 ≤ z)%Z → n = Z.to_nat z :> nat → n = z :> Z.
Proof. lia. Qed.

Section gset_map.
  Context `{EqDecision A, !Countable A, !EqDecision B, !Countable B}.

  Definition gset_map (f : A → B) (g : gset A) : gset B :=
    list_to_set (f <$> elements g).

  Lemma gset_map_empty f : gset_map f ∅ = ∅.
  Proof. by rewrite /gset_map elements_empty /=. Qed.

  Lemma gset_map_singleton f a : gset_map f {[a]} = {[f a]}.
  Proof. by rewrite /gset_map elements_singleton /= right_id_L. Qed.

  Lemma gset_map_union f g g' :
    gset_map f (g ∪ g') = gset_map f g ∪ gset_map f g'.
  Proof.
    revert g'.
    pattern g.
    match goal with |- ?F g => simpl; apply (set_ind_L F) end; set_solver.
  Qed.

  Lemma gset_map_correct1 f g : ∀ a, a ∈ g → (f a) ∈ gset_map f g.
  Proof.
    pattern g.
    match goal with |- ?F g => simpl; apply (set_ind_L F) end; set_solver.
  Qed.

  Lemma gset_map_correct2 f g : ∀ b, b ∈ gset_map f g → ∃ a, b = f a ∧ a ∈ g.
  Proof.
    pattern g.
    match goal with |- ?F g => simpl; apply (set_ind_L F) end; set_solver.
  Qed.

End gset_map.


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
    - rewrite map_fold_empty; set_solver.
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

Section find_one_maximal.
  Context {A B : Type} (f : A → B)
          (R : relation B) `{!RelDecision R} `{!Transitive R}
          (S : relation B) `{!Transitive S} `{!Reflexive S}
          (HRS : ∀ a b, R a b → S a b)
          (HSR : ∀ a b, S a b → a = b ∨ R a b)
          (HRir : ∀ a, ¬ R a a)
          (HRex : ∀ a b, R a b → R b a → False)
          (HSR_trans : ∀ a b c, S a b → R b c → R a c).

    Fixpoint find_one_maximal (candidate : A) (l : list A) :=
      match l with
      | [] => candidate
      | a :: l' => if bool_decide (R (f candidate) (f a)) then
                   find_one_maximal a l'
                 else
                   find_one_maximal candidate l'
      end.

    Lemma find_one_maximal_rel c l : S (f c) (f (find_one_maximal c l)).
    Proof.
      revert c; induction l as [|a l IHl]; intros c; first done.
      destruct (decide (R (f c) (f a))).
      - rewrite /= bool_decide_eq_true_2 //; by etrans; eauto.
      - rewrite /= bool_decide_eq_false_2 //.
    Qed.

  Lemma find_one_maximal_maximal c l y :
    y ∈ l → ¬ R (f (find_one_maximal c l)) (f y).
  Proof.
    revert c; induction l as [|a l IHl]; intros c; first by inversion 1.
    intros [->|Hy]%elem_of_cons.
    - destruct (decide (R (f c) (f a))) as [|Hnot].
      + rewrite /= bool_decide_eq_true_2 //.
        pose proof (find_one_maximal_rel a l) as [ <- | ?]%HSR;
          first by apply HRir.
        intros ?; eapply HRex; eauto.
      + rewrite /= bool_decide_eq_false_2 //.
        intros ?.
        apply Hnot.
        eapply HSR_trans; eauto using find_one_maximal_rel.
    - destruct (decide (R (f c) (f a))) as [|Hnot].
      + rewrite /= bool_decide_eq_true_2 //.
        intros ?; eapply IHl; eauto.
      + rewrite /= bool_decide_eq_false_2 //.
        intros ?; eapply IHl; eauto.
  Qed.

  Lemma find_one_maximal_eq_or_elem_of c l :
    find_one_maximal c l = c ∨ find_one_maximal c l ∈ l.
  Proof.
    revert c; induction l as [|a l IHl]; intros c; first by left.
    destruct (decide (R (f c) (f a))) as [|Hnot].
    - rewrite /= bool_decide_eq_true_2 //.
      destruct (IHl a) as [->|]; by right; constructor.
    - rewrite /= bool_decide_eq_false_2 //.
      destruct (IHl c) as [->|]; first by left.
      by right; constructor.
  Qed.

  Context (HNRS : ∀ a b, ¬ R a b → S b a)
          (min : A)
          (Hmin : ∀ a, S (f min) a).

  Definition sup l := find_one_maximal min l.

  Lemma sup_UB l a : a ∈ l → S (f a) (f (sup l)).
  Proof. by intros Hl; apply HNRS; apply find_one_maximal_maximal. Qed.

  Lemma sup_LUB l u : (∀ a, a ∈ l → S (f a) (f u)) → (S (f (sup l)) (f u)).
  Proof.
    intros Hu.
    rewrite /sup.
    destruct (find_one_maximal_eq_or_elem_of min l) as [->|];
      first by apply Hmin.
    by apply Hu.
  Qed.

  Context `{!RelDecision S} `{!EqDecision A} `{!AntiSymm eq S} `{!Inj eq eq f}.

  Lemma sup_elem_of a l : a ∈ l → sup l ∈ l.
  Proof.
  intros Hal.
  rewrite /sup.
  destruct (find_one_maximal_eq_or_elem_of min l) as [Heq|]; last done.
  rewrite Heq.
  destruct (decide (S (f a) (f min))) as [|Hnz].
  - assert (a = min) as <-; last done.
    eapply inj; first apply _.
    eapply anti_symm; first apply _; auto.
  - exfalso; apply Hnz.
    rewrite -Heq.
    by apply sup_UB.
Qed.

  Lemma sup_mono l l' : (∀ a, a ∈ l → a ∈ l') → S (f (sup l)) (f (sup l')).
  Proof.
    destruct l as [|x l]; first by intros; rewrite /sup /=; auto.
    assert (x ∈ (x :: l)) as Hx by constructor.
    revert Hx.
    generalize (x :: l) as k; clear l; intros l Hxl.
    intros Hll.
    apply sup_UB.
    apply Hll.
    eapply sup_elem_of; eauto.
  Qed.

Lemma sup_equiv `{!AntiSymm S' S} l l' :
  (∀ a, a ∈ l ↔ a ∈ l') → S' (f (sup l)) (f (sup l')).
Proof. intros; eapply anti_symm; first done; apply sup_mono; naive_solver. Qed.

Lemma sup_of_nil : sup [] = min.
Proof. done. Qed.

End find_one_maximal.

Definition nat_sup (l : list nat) := sup id lt 0 l.

Lemma nat_sup_UB l a : a ∈ l → a ≤ (nat_sup l).
Proof. apply (sup_UB id); try apply _; auto with lia. Qed.

Lemma nat_sup_LUB l u : (∀ a, a ∈ l → a ≤ u) → (nat_sup l) ≤ u.
Proof. apply (sup_LUB id); try apply _; simpl; auto with lia. Qed.

Lemma nat_sup_elem_of a l : a ∈ l → nat_sup l ∈ l.
Proof.
  eapply (sup_elem_of id lt le); try apply _; simpl; auto with lia.
Qed.

Lemma nat_sup_mono l l' : (∀ a, a ∈ l → a ∈ l') → (nat_sup l) ≤ (nat_sup l').
Proof.
  eapply (sup_mono id lt le); try apply _; simpl; auto with lia.
Qed.

Lemma nat_sup_equiv l l' : (∀ a, a ∈ l ↔ a ∈ l') → (nat_sup l) = (nat_sup l').
Proof.
  intros; eapply (sup_equiv id lt le) with (S' := eq);
    try apply _; simpl; auto with lia.
Qed.

Lemma nat_sup_of_nil : nat_sup [] = 0.
Proof. apply sup_of_nil. Qed.
