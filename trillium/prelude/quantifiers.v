From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.
From trillium.prelude Require Import classical sigma.

Definition injective {A B} (f : A → B) := ∀ x y, f x = f y → x = y.

Lemma injective_compose {A B C} (f : A → B) (g : B → C) :
  injective f → injective g → injective (λ x, g (f x)).
Proof. intros Hf Hg x y Hxy; apply Hf, Hg; trivial. Qed.

Definition smaller_card A B := ∀ f : B → A, ¬ injective f.

Section quantifiers.
  Context (A : Type) (R : A → A → Prop)
          (Htotal : ∀ x y, R x y ∨ R y x)
          (Htrans : ∀ x y z, R x y → R y z → R x z).

  Definition subset := A → Prop.

  Definition subset_type (S : subset) : Type := sig S.

  Definition cofinal (S : subset) := ∀ x, ∃ y, S y ∧ R x y.

  Definition regular :=
    ∀ (S : subset), cofinal S → ∃ f : A → (subset_type S), injective f.

  Lemma not_cofinal_smaller S :
    ¬ cofinal S → ∃ x, ∀ y, S y → ¬ R x y.
  Proof.
    intros Hncf.
    apply not_forall_exists_not in Hncf as [x Hncf]; eauto 10.
  Qed.

  Definition union {I : Type} (fam : I → subset) : subset := λ x, ∃ i, fam i x.

  Lemma regular_union_of_smaller (I : Type) (fam : I → subset) :
    regular →
    smaller_card I A →
    (∀ i, ¬ cofinal (fam i)) →
    ¬ (cofinal (union fam)).
  Proof.
    intros Hreg HI Hfam Hcnf.
    pose proof (Hreg _ Hcnf) as [f Hf].
    assert (∀ i, ∃ x, ∀ y, fam i y → ¬ R x y) as Hmax.
    { intros i. apply not_cofinal_smaller; auto. }
    apply Choice in Hmax as [g Hg].
    set (Img := λ x, ∃ i, g i = x).
    assert (∀ x : subset_type Img, ∃ i : I, proj1_sig x = g i) as Himgback.
    { intros [? [? ?]]; eauto. }
    apply Choice in Himgback as [h Hh].
    assert (injective h).
    { intros x y Hxy.
      apply sig_eq; rewrite !Hh, Hxy; trivial. }
    assert (¬ cofinal Img) as Himgncnf.
    { intros Himgcnf.
      destruct (Hreg _ Himgcnf) as [h' Hh'].
      apply (HI (λ x, h (h' x))).
      apply injective_compose; auto. }
    apply not_cofinal_smaller in Himgncnf as [z Hz].
    destruct (Hcnf z) as [u [[i Hu1] Hu2]].
    assert (R z (g i)) as Hzgi.
    { pose proof (Hg i _ Hu1).
      destruct (Htotal (g i) u); [tauto|].
      eapply Htrans; eauto. }
    apply Hz in Hzgi; [|unfold Img]; eauto.
  Qed.

  Lemma regular_union_biger (I : Type) (fam : I → subset) :
    regular →
    smaller_card I A →
    (cofinal (union fam)) →
    ∃ i, cofinal (fam i).
  Proof.
    intros Hreg HI Hcnf.
    cut (∃ i, ¬ ¬ cofinal (fam i)).
    { intros [? ?]; eexists; apply NNP_P; eauto. }
    apply not_forall_exists_not.
    intros Hfam.
    eapply regular_union_of_smaller; eauto.
  Qed.

  Context (B : Type) (P : A → B → Prop).

  Definition fiber (b : B) : subset := λ x, P x b.

  Context (Hmono : ∀ x y z, R x y → P y z → P x z).

  Lemma cofinal_fiber_forall (b : B) : cofinal (fiber b) → ∀ x, P x b.
  Proof.
    intros Hb x.
    destruct (Hb x) as (y & Hy1 & Hy2).
    eapply Hmono; eauto.
  Qed.

  Context (Hrefl : ∀ x, R x x).

  Lemma forall_exists_swap :
    regular →
    smaller_card B A →
    (∀ x : A, ∃ y : B, P x y) → ∃ y, ∀ x, P x y.
  Proof.
    intros Hreg HB Hfe.
    destruct (regular_union_biger _ fiber) as [y Hy]; [trivial|trivial| |].
    { intros x. destruct (Hfe x) as [y Hy].
      exists x; split; [|apply Hrefl].
      eexists; eauto. }
    exists y; apply cofinal_fiber_forall; trivial.
  Qed.

End quantifiers.

Example nat_regular : regular nat le.
Proof.
  intros St HS.
  pose proof (Choice _ _ _ HS) as [f Hf].
  set (g :=
         fix g n :=
         match n with
         | 0 => f 0
         | S n' => f (S (g n'))
         end).
  assert (∀ n, St (g n)) as Hg.
  { destruct n; apply Hf. }
  assert (∀ x y, x < y → g x < g y) as Hglt.
  { intros x y; revert x.
    induction y as [|y IHy]; simpl; [lia|].
    intros x Hx.
    destruct (PeanoNat.Nat.eq_dec x y) as [->|].
    - pose proof (Hf (S (g y))) as [_ ?].
      lia.
    - pose proof (Hf (S (g y))) as [_ ?].
      assert (g x < g y).
      { apply IHy; lia. }
      lia. }
  set (G n := exist _ _ (Hg n)).
  exists G.
  intros x y Hxy.
  assert (proj1_sig (G x) = proj1_sig (G y)) by (rewrite Hxy; auto); simpl in *.
  destruct (Compare_dec.lt_eq_lt_dec x y) as [[|]|]; [|trivial; fail|].
  - assert (g x < g y) by (apply Hglt; lia); lia.
  - assert (g y < g x) by (apply Hglt; lia); lia.
Qed.
