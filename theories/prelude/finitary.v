From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.
From aneris.prelude Require Import classical quantifiers sigma.
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
  Context {A} `{!EqDecision A}.

  Section no_fin_inj.
    Context (Hnfin : Finite A → False).

    Lemma no_fin_new_elem_exist (l : list A) : ∃ x, x ∉ l.
    Proof.
      destruct (ExcludedMiddle (∀ x : A, x ∈ l)); last first.
      { apply not_forall_exists_not; done. }
      exfalso; apply Hnfin.
      refine {| enum := remove_dups l |}.
      - apply NoDup_remove_dups.
      - intros; apply elem_of_remove_dups; done.
    Qed.

    Fixpoint no_fin_make_list (l : list A) (n : nat) : list A :=
      match n with
      | 0 => l
      | S n' =>
        no_fin_make_list l n' ++
        [epsilon (no_fin_new_elem_exist (no_fin_make_list l n'))]
      end.

    Lemma no_fin_make_list_length l n :
      length (no_fin_make_list l n) = length l + n.
    Proof.
      induction n as [|n IHn]; [simpl; lia|].
      simpl; rewrite app_length, IHn; simpl; lia.
    Qed.

    Lemma no_fin_make_list_prefix l n1 n2 :
      n1 ≤ n2 → (no_fin_make_list l n1) `prefix_of` (no_fin_make_list l n2).
    Proof.
      induction 1 as [|n2 IHn12]; [done|].
      simpl; apply prefix_app_r; done.
    Qed.

    Lemma no_fin_make_list_NoDup l n : NoDup l → NoDup (no_fin_make_list l n).
    Proof.
      revert l; induction n; intros l Hl; [done|].
      simpl.
      apply NoDup_app; split; [auto; done|].
      split; [|apply NoDup_singleton].
      intros x Hx ->%elem_of_list_singleton.
      apply (epsilon_correct _ (no_fin_new_elem_exist (no_fin_make_list l n)));
        done.
    Qed.

    Definition no_fin_make_inj_fun (n : nat) : A :=
      default (epsilon (no_fin_new_elem_exist [])) (no_fin_make_list [] (S n) !! n).

    Lemma no_fin_make_inj_fun_inj : injective no_fin_make_inj_fun.
    Proof.
      assert (∀ n m, n ≤ m → no_fin_make_inj_fun n = no_fin_make_inj_fun m → n = m)
        as Hnm.
      { intros n m Hnm Hfnm.
        unfold no_fin_make_inj_fun in Hfnm.
        pose proof (lookup_lt_is_Some_2 (no_fin_make_list [] (S n)) n) as [k Hk].
        { rewrite no_fin_make_list_length; lia. }
        pose proof (lookup_lt_is_Some_2 (no_fin_make_list [] (S m)) m) as [l Hl].
        { rewrite no_fin_make_list_length; lia. }
        rewrite Hk, Hl in Hfnm; simpl in Hfnm; simplify_eq.
        apply (NoDup_lookup (no_fin_make_list [] (S m)) n m l); [| |done].
        - apply no_fin_make_list_NoDup, NoDup_nil_2.
        - apply  (prefix_lookup
                    (no_fin_make_list [] (S n)) (no_fin_make_list [] (S m)) n l);
            [done|].
          apply no_fin_make_list_prefix; lia.
      }
      intros n m.
      destruct (decide (n < m)).
      - apply Hnm; lia.
      - intros; symmetry; apply Hnm; [lia|done].
    Qed.

  End no_fin_inj.

  Lemma smaller_card_nat_finite : smaller_card A nat → Finite A.
  Proof.
    intros HA.
    apply (epsilon (P := λ _, True)).
    destruct (ExcludedMiddle (∃ _ : Finite A, True)); [done|].
    assert (∀ x : Finite A, False) as Hnfin.
    { cut (∀ x : Finite A, ¬ True); [tauto|].
      eapply not_exists_forall_not; done. }
    exfalso.
    apply (HA (no_fin_make_inj_fun Hnfin)).
    apply no_fin_make_inj_fun_inj.
  Qed.

End smaller_card_nat_finite.

(* move *)

Lemma NoDup_list_prod {A B} (l : list A) (l' : list B) :
  NoDup l → NoDup l' → NoDup (list_prod l l').
Proof.
  revert l'; induction l as [|a l]; intros l' Hl Hl'.
  { apply NoDup_nil_2. }
  inversion Hl; simplify_eq.
  simpl.
  apply NoDup_app; split; [|split].
  - apply NoDup_fmap; [|done].
    intros ? ?; inversion 1; trivial.
  - intros [x y] [z [Hz1 Hz2]]%elem_of_list_fmap; simplify_eq.
    intros Hin%elem_of_list_In.
    apply in_prod_iff in Hin as [Hin1%elem_of_list_In Hin2]; done.
  - apply IHl; done.
Qed.

Section finite_lemmas.
  Context `{!EqDecision A} `{!EqDecision B}.

  Program Instance sig_finite_and (P : A → Prop) (Q : B → Prop)
        `{!∀ x, Decision (P x)} `{!∀ x, ProofIrrel (P x)}
        `{!∀ x, Decision (Q x)} `{!∀ x, ProofIrrel (Q x)}
        (HfP : Finite {x : A | P x})
        (HfQ : Finite {x : B | Q x}) :
    Finite {x : A * B | P (fst x) ∧ (Q (snd x))} :=
    {| enum :=
         (λ x, sig_prod_and x.1 x.2)
           <$> (list_prod (@enum _ _ HfP) (@enum _ _ HfQ)) |}.
  Next Obligation.
  Proof.
    intros.
    apply NoDup_fmap.
    { intros [[] []] [[] []].
      unfold sig_prod_and; simpl; inversion 1; simplify_eq.
      f_equal; apply sig_eq; done. }
    apply NoDup_list_prod; apply NoDup_enum.
  Qed.
  Next Obligation.
  Proof.
    intros ? ? ? ? ? ? ? ? [[a b] [Ha Hb]].
    apply elem_of_list_fmap.
    exists (a ↾ Ha, b ↾ Hb); split.
    { apply sig_eq; done. }
    apply elem_of_list_In, in_prod_iff.
    split; apply elem_of_list_In, elem_of_enum.
  Qed.

  Program Instance sig_finite_eq1 (a : A) : Finite {x : A | x = a} :=
    {| enum := [a ↾ eq_refl] |}.
  Next Obligation.
  Proof. intros; apply NoDup_singleton. Qed.
  Next Obligation.
  Proof. intros ? [? ?]; apply elem_of_list_singleton; apply sig_eq; done. Qed.

  Program Instance sig_finite_eq2 (a : A) : Finite {x : A | a = x} :=
    {| enum := [a ↾ eq_refl] |}.
  Next Obligation.
  Proof. intros; apply NoDup_singleton. Qed.
  Next Obligation.
  Proof. intros ? [? ?]; apply elem_of_list_singleton; apply sig_eq; done. Qed.

  Program Instance sig_finite_or (P : A → Prop) (Q : A → Prop)
          `{!∀ x, Decision (P x)} `{!∀ x, ProofIrrel (P x)}
          `{!∀ x, Decision (Q x)} `{!∀ x, ProofIrrel (Q x)}
          (HfP : Finite {x : A | P x})
          (HfQ : Finite {x : A | Q x}) :
    Finite {x : A | P x ∨ Q x} :=
    {| enum :=
         remove_dups ((sig_prod_or_l <$> (@enum _ _ HfP))
            ++ (sig_prod_or_r <$> (@enum _ _ HfQ))) |}.
  Next Obligation.
  Proof. intros; apply NoDup_remove_dups. Qed.
  Next Obligation.
  Proof.
    intros ? ? ? ? ? ? ? ? [a [Ha|Ha]].
    - pose proof (@elem_of_enum _ _ HfP (a ↾ Ha)).
      apply elem_of_remove_dups.
      apply elem_of_app.
      left.
      apply elem_of_list_fmap; eexists; split; last done; done.
    - pose proof (@elem_of_enum _ _ HfQ (a ↾ Ha)).
      apply elem_of_remove_dups.
      apply elem_of_app.
      right.
      apply elem_of_list_fmap; eexists; split; last done; done.
  Qed.

End finite_lemmas.

Lemma finite_eq_dec_irrel {A} (HA HA' : EqDecision A) :
  @Finite _ HA → @Finite _ HA'.
Proof.
  intros [e HeND Heall].
  refine {| enum := e |}; [done|done].
Qed.
