From iris.algebra Require Import gmap.

Lemma nat_Z_eq (n : nat) (z : Z) :
  (0 ≤ z)%Z → n = Z.to_nat z :> nat → n = z :> Z.
Proof. lia. Qed.

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

Lemma not_inj_fn `{EqDecision A} {B} (x y : A) (f : A → B) `{!Inj (=) (=) f} :
  f x ≠ f y → x ≠ y.
Proof.
  intros Hf.
  destruct (bool_decide (x = y)) eqn:Heq.
  - apply bool_decide_eq_true_1 in Heq. simplify_eq.
  - by apply bool_decide_eq_false_1 in Heq.
Qed.

Lemma nth_error_lookup {A} (l : list A) (i : nat) x :
  nth_error l i  = Some x → l !! i = Some x.
Proof.
  revert i. induction l as [|?? IHl]; destruct i; auto.
    by apply IHl.
Qed.

Lemma take_S_r_nth `{A : Type}:
  ∀  (l : list A) (n : nat) (x : A),
    nth_error l n = Some x →  take (n + 1) l = take n l ++ [x].
Proof. induction l; intros []; naive_solver eauto with f_equal. Qed.

Lemma map_nth_error_inv { A B}: forall n (l: list A) d (f: A → B),
    (∀ x y, f x = f y → x = y) →
    nth_error (map f l) n = Some (f d) → nth_error l n = Some d.
Proof.
  induction n; intros [|] ??? H; simpl in *; inversion H; eauto using f_equal.
Qed.

Lemma map_lookup_Some {A B} (f : A → B) (l : list A) (i : nat) (k : B) :
  map f l !! i = Some k →
  ∃ a, k = f a ∧ l !! i = Some a.
Proof.
  revert i. induction l; [done|].
  intros [] Hmap.
  - eexists. by inversion Hmap.
  - by apply IHl in Hmap.
Qed.

Lemma list_to_set_size `{EqDecision A, !Countable A} l :
  NoDup l →
  size (list_to_set l : gset A) = length l.
Proof.
  induction l; [done|].
  rewrite NoDup_cons /=; intros [? ?].
  rewrite size_union ?size_singleton ?IHl //.
  set_solver.
Qed.

Lemma rtc_destutter {A} (R : relation A) x1 x2 :
  rtc (λ x x', x = x' ∨ R x x') x1 x2 → rtc R x1 x2.
Proof.
  apply (rtc_ind_l (λ x, rtc R x x2)).
  { constructor. }
  intros ? ? [-> | ?] ? ?; [done|].
  by econstructor.
Qed.

Lemma gt_exists_S_n n m :
  n < m → ∃ m', m = S m'.
Proof. destruct n, m; [lia|eauto with lia|lia|eauto with lia]. Qed.

Lemma rt_rtc_same {A} (R : relation A) `{!Reflexive R, !Transitive R} : ∀ x y, rtc R x y ↔ R x y.
Proof. intros ??; split; last by apply rtc_once. induction 1; first done. etrans; eauto. Qed.

Global Instance fin_inh n : Inhabited (fin (S n)) := populate 0%fin.

Lemma difference_difference_union `{Countable T} (A B C : gset T) :
  C ⊆ A -> A ∖ (B ∖ C) = A ∖ B ∪ C.
Proof. rewrite sets.set_eq. intros. destruct (decide (x ∈ C)); set_solver. Qed.
