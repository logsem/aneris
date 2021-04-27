From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.
From aneris.prelude Require Import classical quantifiers.
From stdpp Require Import finite fin_sets.

Section finite_smaller_card_nat.
  Context {A} `{!EqDecision A}.

  Fixpoint list_generated_by (f : nat → A) (n : nat) : list A :=
    match n with
    | O => [f 0]
    | S n => f (S n) :: list_generated_by f n
    end.

  Lemma list_generated_by_length (f : nat → A) n :
    length (list_generated_by f n) = S n.
  Proof. induction n as [|? IHn]; [|simpl; rewrite IHn]; done. Qed.

  Lemma elem_of_list_generated_by (f : nat → A) n x :
    x ∈ list_generated_by f n ↔ ∃ m, m ≤ n ∧ x = f m.
  Proof.
    split.
    - induction n; simpl.
      + intros ->%elem_of_list_singleton; eauto.
      + intros [->|Hn]%elem_of_cons; [by eauto|].
        apply IHn in Hn as (?&?&?); eauto.
    - intros [m [Hm1 ->]].
      revert m Hm1; induction n; intros m Hm.
      + replace m with 0 by lia.
        apply elem_of_list_singleton; done.
      + destruct (decide (m = S n)) as [->|].
        * simpl; apply elem_of_cons; auto.
        * simpl; apply elem_of_cons; auto with lia.
  Qed.

  Lemma list_generated_by_NoDup (f : nat → A) n :
    injective f → NoDup (list_generated_by f n).
  Proof.
    intros Hf.
    induction n; simpl.
    - repeat constructor; set_solver.
    - constructor; [|done].
      intros (?&?&?%Hf)%elem_of_list_generated_by; lia.
  Qed.

  Lemma finite_smaller_card_nat : Finite A → smaller_card A nat.
  Proof.
    destruct 1 as [enum Henum Hin].
    intros f Hf.
    assert (length (list_generated_by f (length enum)) ≤ length enum) as Hlen.
    { apply submseteq_length.
      apply NoDup_submseteq; auto using list_generated_by_NoDup. }
    rewrite list_generated_by_length in Hlen; lia.
  Qed.

End finite_smaller_card_nat.

Definition surjective {A B} (f : A → B) := ∀ y, ∃ x, f x = y.

Section smaller_card_nat_finite.
  Context {A} `{!Inhabited A} `{!EqDecision A}.

  Section no_surj_inj.
    Context (Hnj : ∀ h : nat → A, ¬ surjective h).

    Lemma nosurj_new_elem_exist (l : list A) : ∃ x, x ∉ l.
    Proof.
      specialize (Hnj (λ n, nth n l inhabitant)).
      apply not_forall_exists_not in Hnj as [x Hx].
      exists x.
      intros [n Hn]%elem_of_list_lookup_1.
      apply (nth_lookup_Some _ _ inhabitant) in Hn.
      eapply not_exists_forall_not in Hx; eauto.
    Qed.

    Fixpoint nosurj_make_list (l : list A) (n : nat) : list A :=
      match n with
      | 0 => l
      | S n' =>
        nosurj_make_list l n' ++
        [epsilon (nosurj_new_elem_exist (nosurj_make_list l n'))]
      end.

    Lemma nosurj_make_list_length l n :
      length (nosurj_make_list l n) = length l + n.
    Proof.
      induction n as [|n IHn]; [simpl; lia|].
      simpl; rewrite app_length, IHn; simpl; lia.
    Qed.

    Lemma nosurj_make_list_prefix l n1 n2 :
      n1 ≤ n2 → (nosurj_make_list l n1) `prefix_of` (nosurj_make_list l n2).
    Proof.
      induction 1 as [|n2 IHn12]; [done|].
      simpl; apply prefix_app_r; done.
    Qed.

    Lemma nosurj_make_list_NoDup l n : NoDup l → NoDup (nosurj_make_list l n).
    Proof.
      revert l; induction n; intros l Hl; [done|].
      simpl.
      apply NoDup_app; split; [auto; done|].
      split; [|apply NoDup_singleton].
      intros x Hx ->%elem_of_list_singleton.
      apply (epsilon_correct _ (nosurj_new_elem_exist (nosurj_make_list l n)));
        done.
    Qed.

    Definition nosurj_make_inj_fun (n : nat) : A :=
      default inhabitant (nosurj_make_list [] (S n) !! n).

    Lemma nosurj_make_inj_fun_inj : injective nosurj_make_inj_fun.
    Proof.
      assert (∀ n m, n ≤ m → nosurj_make_inj_fun n = nosurj_make_inj_fun m → n = m)
        as Hnm.
      { intros n m Hnm Hfnm.
        unfold nosurj_make_inj_fun in Hfnm.
        pose proof (lookup_lt_is_Some_2 (nosurj_make_list [] (S n)) n) as [k Hk].
        { rewrite nosurj_make_list_length; lia. }
        pose proof (lookup_lt_is_Some_2 (nosurj_make_list [] (S m)) m) as [l Hl].
        { rewrite nosurj_make_list_length; lia. }
        rewrite Hk, Hl in Hfnm; simpl in Hfnm; simplify_eq.
        apply (NoDup_lookup (nosurj_make_list [] (S m)) n m l); [| |done].
        - apply nosurj_make_list_NoDup, NoDup_nil_2.
        - apply  (prefix_lookup
                    (nosurj_make_list [] (S n)) (nosurj_make_list [] (S m)) n l);
            [done|].
          apply nosurj_make_list_prefix; lia.
      }
      intros n m.
      destruct (decide (n < m)).
      - apply Hnm; lia.
      - intros; symmetry; apply Hnm; [lia|done].
    Qed.

  End no_surj_inj.

  Definition least_domain_subset_including (h : nat → A) (x : A) : subset nat :=
    λ k, ∀ n, (∃ m, m ≤ n ∧ h m = x) → k ≤ n.

  Lemma least_domain_subset_including_all_not_cofinal (h : nat → A) :
    surjective h → ∀ x, ¬ cofinal nat le (least_domain_subset_including h x).
  Proof.
    intros Hh x Hcf.
    destruct (Hh x) as [k Hk].
    destruct (Hcf (S k)) as [l [Hl1 Hl2]].
    specialize (Hl1 k).
    assert (l ≤ k); [eauto|lia].
  Qed.

  Lemma serjective_pre_image_bounded (h : nat → A) (Hhsurj : surjective h) :
    smaller_card A nat → ∃ n, ∀ a, ∃ i, i ≤ n ∧ h i = a.
  Proof.
    intros Hsmc.
    assert (¬ cofinal
              nat le (quantifiers.union _ (least_domain_subset_including h)))
      as Hncf.
    { intros [x Hx]%regular_union_biger; auto using nat_regular with lia.
      apply least_domain_subset_including_all_not_cofinal in Hx; done. }
    apply not_forall_exists_not in Hncf as [n Hncf].
    exists n; intros a.
    destruct (dec_inh_nat_subset_has_unique_least_element (λ n, h n = a))
      as [i [[Hi1 Hi2] Hi3]]; [|apply Hhsurj; done|].
    { intros k; destruct (decide (h k = a)); eauto. }
    exists i; split; [|done].
    destruct (decide (i < n)); [lia|].
    exfalso; apply Hncf.
    exists i; split; [|lia].
    exists a; intros m [j [Hj1 Hj2]].
    etrans; [apply Hi2; apply Hj2|lia].
  Qed.

  Lemma smaller_card_nat_finite `{!EqDecision A} :
    smaller_card A nat → Finite A.
  Proof.
    intros HA.
    apply (epsilon (P := λ _, True)).
    destruct (ExcludedMiddle (∃ h : nat → A, surjective h)) as [[h Hh]|Hnsurj].
    - destruct (serjective_pre_image_bounded h) as [n Hn]; [done|done|].
      unshelve eexists {| enum := remove_dups (list_generated_by h n) |};
        [| |done].
      + apply NoDup_remove_dups.
      + intros a; apply elem_of_remove_dups.
        destruct (Hn a) as [i [Hi1 Hi2]].
        apply elem_of_list_generated_by; eauto.
    - assert (∀ h : nat → A, ¬ surjective h) as Hnsurj'.
      { apply not_exists_forall_not; done. }
      specialize (HA (nosurj_make_inj_fun Hnsurj')).
      exfalso; apply HA.
      apply nosurj_make_inj_fun_inj.
  Qed.

End smaller_card_nat_finite.

Section finite_lemmas.
  Context `{!EqDecision A} `{!EqDecision B}.

  Lemma sig_finite_and (P : A → Prop) (Q : B → Prop)
        `{!∀ x, Decision (P x)} `{!∀ x, ProofIrrel (P x)}
        `{!∀ x, Decision (Q x)} `{!∀ x, ProofIrrel (Q x)} :
    Finite {x : A | P x} →
    Finite {x : B | Q x} →
    Finite {x : A * B | P (fst x) ∧ (Q (snd x))}.
  Proof.
  Admitted.

End finite_lemmas.
