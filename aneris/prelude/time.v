(** Realisation of the time using vector clocs. *)

From aneris.aneris_lang Require Import lang.
From aneris.prelude Require Import misc strings.
From stdpp Require Import list sets.

Definition vector_clock := list nat.

(** Alternatively the specs in vector_clock.v can use
    the following instead of the is_vc predicate. *)
Fixpoint vector_clock_to_val (t : vector_clock) : val :=
  match t with
  | [] => NONEV
  | a :: t' => SOMEV (#a, vector_clock_to_val t')
  end.

#[global] Program Instance Inj_vector_clock : Inj eq eq vector_clock_to_val.
Next Obligation.
  intros x; induction x as [ | h x' IH]; intros y Heq;
    destruct y; [done | done | done |].
  inversion Heq as [[Hh Ht]].
  apply f_equal2; [by apply Nat2Z.inj | by apply IH].
Qed.

Definition vector_clock_le (t t' : vector_clock) := Forall2 le t t'.

Definition vector_clock_lt (t t' : vector_clock) :=
  vector_clock_le t t' ∧ Exists (λ x, x.1 < x.2) (zip t t').

#[global] Instance vector_clock_le_dec : RelDecision vector_clock_le.
Proof. apply Forall2_dec; apply _. Qed.

#[global] Instance vector_clock_lt_dec : RelDecision vector_clock_lt.
Proof. intros ? ?; apply and_dec; apply _. Qed.

#[global] Instance vector_clock_le_PO : PartialOrder vector_clock_le.
Proof.
  split; first split.
  - intros ?; rewrite /vector_clock_le /=; reflexivity.
  - intros ???; rewrite /vector_clock_le /=; etrans; eauto.
  - intros ? ?; rewrite /vector_clock_le /=.
    revert y; induction x as [|a x].
    + by inversion 1; simplify_eq.
    + intros [|b y]; first by inversion 1.
      do 2 inversion 1; simplify_eq.
      auto with f_equal lia.
Qed.

Lemma vector_clock_lt_irreflexive x : ¬ vector_clock_lt x x.
Proof.
  intros [? (?&(?&?&?&?&?&?)%elem_of_lookup_zip_with_1&?)%Exists_exists];
    simplify_eq/=; lia.
Qed.

#[global] Instance vector_clock_lt_transitive : Transitive vector_clock_lt.
Proof.
  intros x y z
         [Hxy1 (?&(i&xi&yi&?&Hi1&Hi2)%elem_of_lookup_zip_with_1&?)%Exists_exists]
         [Hyz1 Hyz2];
    simplify_eq/=.
  split; first etrans; eauto.
  apply Exists_exists.
  destruct (Forall2_lookup_l _ _ _ _ _ Hyz1 Hi2) as (zi&?&?).
  exists (xi, zi); split; last by simpl; lia.
  apply elem_of_lookup_zip_with; eauto 10.
Qed.

Lemma vector_clock_lt_le t t' : vector_clock_lt t t' → vector_clock_le t t'.
Proof. by intros [? ?]. Qed.

Lemma vector_clock_lt_exclusion t t' :
  vector_clock_lt t t' → vector_clock_lt t' t → False.
Proof.
  intros [Htt'1 (?&(i&xi&yi&?&Hi1&Hi2)%elem_of_lookup_zip_with_1&?)%Exists_exists]
         [Ht't1 Ht't2]; simplify_eq/=.
  pose proof (Forall2_lookup_lr _ _ _ _ _ _ Ht't1 Hi2 Hi1); lia.
Qed.

Lemma vector_clock_le_eq_or_lt t t' :
  vector_clock_le t t' → t = t' ∨ vector_clock_lt t t'.
Proof.
  intros Hlt.
  destruct (decide (t = t')) as [|Hneq]; first by left.
  right.
  split; first done.
  revert t' Hlt Hneq.
  induction t as [|a t IHt].
  - by inversion 1.
  - intros [|b t']; inversion 1; simplify_eq/=.
    intros.
    destruct (decide (a = b)); last by constructor 1; simpl; lia.
    subst.
    constructor 2; apply IHt; auto with f_equal.
Qed.

Lemma vector_clock_le_lt_trans t t' t'' :
  vector_clock_le t t' → vector_clock_lt t' t'' →
  vector_clock_lt t t''.
Proof.
  intros Hle [? Hlt]; split; first by etrans; eauto.
  apply Exists_exists in Hlt as
      (?&(i&xi&yi&?&Hi1&Hi2)%elem_of_lookup_zip_with_1&?); simplify_eq/=.
  destruct (Forall2_lookup_r _ _ _ _ _ Hle Hi1) as (zi&?&?).
  apply Exists_exists.
  eexists (zi, yi); split; last by simpl; lia.
  eapply elem_of_lookup_zip_with; eauto 10.
Qed.

Lemma vector_clock_lt_le_trans t t' t'' :
  vector_clock_lt t t' → vector_clock_le t' t'' →
  vector_clock_lt t t''.
Proof.
  intros [? Hlt] Hle; split; first by etrans; eauto.
  apply Exists_exists in Hlt as
      (?&(i&xi&yi&?&Hi1&Hi2)%elem_of_lookup_zip_with_1&?); simplify_eq/=.
  destruct (Forall2_lookup_l _ _ _ _ _ Hle Hi2) as (zi&?&?).
  apply Exists_exists.
  eexists (xi, zi); split; last by simpl; lia.
  eapply elem_of_lookup_zip_with; eauto 10.
Qed.

  Definition incr_time (t : vector_clock) (i : nat) :=
    <[ i := S (default 0 (t !! i)) ]> t.

  Lemma incr_time_length t i : length (incr_time t i) = length t.
  Proof. by rewrite /incr_time insert_length. Qed.

  Lemma incr_time_proj t i k :
    t !! i = Some k → (incr_time t i) !! i = Some (S k).
  Proof.
    rewrite /incr_time; intros Heq.
    rewrite list_lookup_insert; last by apply lookup_lt_is_Some_1; eauto.
    rewrite !Heq; done.
  Qed.

  Lemma incr_time_proj_neq t i j : i ≠ j → (incr_time t i) !! j = t !! j.
  Proof. apply list_lookup_insert_ne. Qed.

  Lemma incr_time_lt t i : i < length t → vector_clock_lt t (incr_time t i).
  Proof.
    intros Hit.
    destruct (lookup_lt_is_Some_2 t i) as [q Hq]; first done.
    split.
    - eapply Forall2_lookup; intros j.
      destruct (decide (i = j)) as [->|].
      + erewrite Hq, incr_time_proj; last done.
        constructor; auto.
      + rewrite incr_time_proj_neq; done.
    - apply Exists_exists.
      exists (q, S q); split; last by auto.
      apply elem_of_lookup_zip_with.
      eexists i, _, _; split_and!; auto.
      erewrite incr_time_proj; eauto.
  Qed.

Section Compute_Maximals.
  Context `{!EqDecision T, !Countable T} (f : T → vector_clock).

  #[global] Instance: RelDecision (λ x y, vector_clock_lt (f x) (f y)).
  Proof. solve_decision. Qed.

  Definition compute_maximals_as_list (g : gset T) : list T :=
    let el := elements g in
    (filter (λ x : T, (Forall (λ y, ¬ vector_clock_lt (f x) (f y)) el)) el).

  Definition compute_maximals (g : gset T) : gset T :=
    list_to_set (compute_maximals_as_list g).

  Lemma elem_of_compute_maximals_as_list1 g x :
    x ∈ compute_maximals_as_list g →
    x ∈ g ∧ ∀ y, y ∈ g → ¬ vector_clock_lt (f x) (f y).
  Proof.
    intros Ht.
    apply elem_of_list_filter in Ht as [Ht1 Ht2%elem_of_elements].
    split; first done.
    intros.
    eapply Forall_forall in Ht1; eauto.
    by apply elem_of_elements.
  Qed.

  Lemma elem_of_compute_maximals_as_list2 g x :
    x ∈ g → (∀ y, y ∈ g → ¬ vector_clock_lt (f x) (f y)) →
    x ∈ compute_maximals_as_list g.
  Proof.
    intros Ht1 Ht2.
    apply elem_of_list_filter; split; last by apply elem_of_elements.
    apply Forall_forall; intros ?; rewrite elem_of_elements; auto.
  Qed.

  Lemma compute_maximals_as_list_NoDup g : NoDup (compute_maximals_as_list g).
  Proof.
    apply NoDup_filter, NoDup_elements.
  Qed.

  Lemma elem_of_compute_maximals_as_list_union_singleton g z x:
    z ∈ compute_maximals_as_list g →
    z ∈ compute_maximals_as_list ({[x]} ∪ g) ∨
    (vector_clock_lt (f z) (f x) ∧ x ∈ compute_maximals_as_list ({[x]} ∪ g)).
  Proof.
    intros [Hz1 Hz2]%elem_of_compute_maximals_as_list1.
    destruct (decide (vector_clock_lt (f z) (f x))).
    - right; split; first done.
      apply elem_of_compute_maximals_as_list2; first set_solver.
      intros y [Hy%elem_of_singleton_1|Hy]%elem_of_union; first subst.
      + apply vector_clock_lt_irreflexive.
      + intros ?; apply (Hz2 y); first done.
        etrans; eauto.
    - left.
      apply elem_of_compute_maximals_as_list2; first set_solver.
      intros y [?%elem_of_singleton_1|]%elem_of_union; first subst; auto.
  Qed.

  Lemma find_one_maximal_in_maximals x g :
    x ∈ g →
    find_one_maximal f vector_clock_lt x (elements g)
      ∈ compute_maximals_as_list g.
  Proof.
    intros Hx.
    apply elem_of_compute_maximals_as_list2.
    - destruct (find_one_maximal_eq_or_elem_of f vector_clock_lt x (elements g))
        as [->|]; first done.
      by apply elem_of_elements.
    - intros ? ?%elem_of_elements.
      apply (find_one_maximal_maximal f vector_clock_lt vector_clock_le);
        eauto using vector_clock_le_eq_or_lt, vector_clock_lt_irreflexive,
        vector_clock_lt_exclusion, vector_clock_le_lt_trans, vector_clock_lt_le.
  Qed.

  Lemma compute_maximals_as_list_correct g x :
    x ∈ g →
    ∃ y, y ∈ compute_maximals_as_list g ∧ vector_clock_le (f x) (f y).
  Proof.
    intros Hx.
    exists (find_one_maximal f vector_clock_lt x (elements g));
      split.
    - by apply find_one_maximal_in_maximals.
    - apply (find_one_maximal_rel f vector_clock_lt vector_clock_le);
        eauto using vector_clock_lt_le.
  Qed.

  Definition compute_maximum (g : gset T) : option T :=
  match (compute_maximals_as_list g) with
  | [] => None
  | t :: l =>
    match l with
    | [] => Some t
    | _ => None
    end
  end.

  Definition IsMaximals (g g' : gset T) :=
    ∀ t : T, t ∈ g' ↔ t ∈ g ∧ ∀ t' : T, t' ∈ g → ¬ vector_clock_lt (f t) (f t').

  Definition IsMaximum (g : gset T) (mx : T) :=
    mx ∈ g ∧ ∀ t, t ∈ g → (¬ t = mx) → vector_clock_lt (f t) (f mx).

  Lemma compute_maximals_correct
        (g : gset T) : IsMaximals g (compute_maximals g).
  Proof.
    rewrite /compute_maximals.
    intros t; split.
    - intros Ht%elem_of_list_to_set.
      by apply elem_of_compute_maximals_as_list1.
    - intros [Ht1 Ht2].
      apply elem_of_list_to_set.
      by apply elem_of_compute_maximals_as_list2.
  Qed.

  Lemma compute_maximum_correct (g : gset T) :
    (∀ x y, x ∈ g → y ∈ g → f x = f y → x = y) →
    (∀ x, compute_maximum g = Some x ↔ IsMaximum g x).
  Proof.
    intros Hginj.
    rewrite /compute_maximum.
    intros x; split; intros Hx.
    - destruct (compute_maximals_as_list g) as [|z []] eqn:Heql; simplify_eq/=.
      assert (∀ y, y ∈ compute_maximals_as_list g ↔ y = x) as Hx.
      { rewrite Heql; set_solver. }
      split.
      + by apply elem_of_compute_maximals_as_list1; apply Hx.
      + intros t Ht Htx.
        pose proof (compute_maximals_as_list_correct _ _ Ht) as (y & Hy1 & Hy2).
        apply Hx in Hy1; subst.
        apply vector_clock_le_eq_or_lt in Hy2 as [Hy2|Hy2]; last done.
        contradict Htx; apply Hginj; auto.
        by apply elem_of_compute_maximals_as_list1, Hx.
    - destruct (compute_maximals_as_list g) as [|z []] eqn:Heql.
      + destruct Hx as [Hx1 Hx2].
        apply compute_maximals_as_list_correct in Hx1 as (y & Hy1 & Hy2).
        rewrite Heql in Hy1; eapply elem_of_nil in Hy1; done.
      + destruct Hx as [Hx1 Hx2].
        destruct (decide (z = x)) as [->|Hneq]; first done.
        pose proof (elem_of_compute_maximals_as_list1 g z) as [Hz1 Hz2].
        { rewrite Heql; constructor. }
        specialize (Hz2 x Hx1).
        specialize (Hx2 _ Hz1 Hneq); done.
      + destruct Hx as [Hx1 Hx2].
        assert (z ≠ x ∨ t ≠ x) as [Hzx|Htx].
        { destruct (decide (z = x)); last by eauto.
          destruct (decide (t = x)); last by eauto.
          pose proof (compute_maximals_as_list_NoDup g) as Hnd.
          rewrite Heql in Hnd.
          apply NoDup_cons in Hnd as [[Hneq1 Hnin1]%not_elem_of_cons Hnd].
          simplify_eq. }
        * assert (z ∈ compute_maximals_as_list g) as Hzmg.
          { rewrite Heql; repeat constructor. }
          pose proof (elem_of_compute_maximals_as_list1 g z Hzmg) as [Hzg Hz].
          exfalso; by eapply Hz; last apply Hx2.
        * assert (t ∈ compute_maximals_as_list g) as Htmg.
          { rewrite Heql; repeat constructor. }
          pose proof (elem_of_compute_maximals_as_list1 g t Htmg) as [Htg Ht].
          exfalso; by eapply Ht; last apply Hx2.
  Qed.

End Compute_Maximals.
