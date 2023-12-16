From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.
From trillium.prelude Require Import
     classical quantifiers sigma classical_instances.
From stdpp Require Import finite fin_sets gmap list.

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
        - apply  (prefix_lookup_Some
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

  Program Definition sig_finite_and2 (P : A → Prop) (Q : A → Prop)
        `{!∀ x, Decision (P x)} `{!∀ x, ProofIrrel (P x)}
        `{!∀ x, Decision (Q x)} `{!∀ x, ProofIrrel (Q x)}
        (HfP : Finite {x : A | P x}) :
    Finite {x : A | P x ∧ Q x} :=
    {| enum := sig_and_list P Q (@enum _ _ HfP) |}.
  Next Obligation.
  Proof.
    intros.
    assert (NoDup (enum {x : A | P x})) as HNoDup by apply NoDup_enum.
    induction enum as [|e enum IHenum]; [by apply NoDup_nil|]=> /=.
    destruct (decide (Q (`e))); [|by eapply IHenum, NoDup_cons_1_2].
    apply NoDup_cons.
    split; [|by eapply IHenum, NoDup_cons_1_2].
    apply NoDup_cons in HNoDup as [HNoDup1 HNoDup2].
    intros Hin. apply HNoDup1.
    by eapply sig_and_list_le.
  Qed.
  Next Obligation.
  Proof.
    intros.
    assert (∀ (x : {x : A | P x}), x ∈ enum {x : A | P x})
      as Hin by apply elem_of_enum.
    destruct x as [x [HP HQ]].
    specialize (Hin (exist _ _ HP)).
    induction enum as [|e enum IHenum]; [by apply elem_of_nil in Hin|].
    apply elem_of_cons in Hin as [Hin|Hin]; simplify_eq /=.
    - case_decide as HQ'; [|done].
      pose proof (proof_irrel HQ HQ') as <-; simplify_eq.
      apply elem_of_cons. by left.
    - case_decide; [right|]; by apply IHenum.
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
          `{!EqDecision {x : A | P x ∨ Q x}}
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
    intros ? ? ? ? ? ? ? ? ? [a [Ha|Ha]].
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

Section in_gset_finite.
  Context `{!EqDecision A, !Countable A}.
  Context {P : A → Prop} `{!∀ x : A, ProofIrrel (P x)}.

  Local Instance: ∀ x, Decision (P x).
  Proof. intros ?; apply make_decision. Qed.

  Program Fixpoint Forall_to_sig (l : list A) : Forall P l → list (sig P) :=
    match l as u return Forall P u → list (sig P) with
    | [] => λ _, []
    | a :: l' => λ Hal, (exist P a _) :: Forall_to_sig l' _
    end.
  Next Obligation.
  Proof. intros ?; inversion 1; simplify_eq; done. Qed.
  Next Obligation.
  Proof. intros ?; inversion 1; simplify_eq; done. Qed.

  Lemma elem_of_Forall_to_sig_1 l HPl x : x ∈ Forall_to_sig l HPl → `x ∈ l.
  Proof.
    revert HPl; induction l as [|a l IHl]; simpl; intros HPl Hx.
    - by apply elem_of_nil in Hx.
    - apply elem_of_cons; apply elem_of_cons in Hx as [->|]; simpl in *; eauto.
  Qed.

  Lemma elem_of_Forall_to_sig_2 l HPl x :
    x ∈ l → ∃ Hx, x ↾ Hx ∈ Forall_to_sig l HPl.
  Proof.
    revert HPl; induction l as [|a l IHl]; simpl; intros HPl Hx.
    - by apply elem_of_nil in Hx.
    - inversion HPl as [|? ? Ha HPl']; simplify_eq.
      apply elem_of_cons in Hx as [->|]; simpl in *.
      + exists Ha; apply elem_of_cons; left; apply sig_eq; done.
      + edestruct IHl as [Hx Hxl]; first done.
        exists Hx; apply elem_of_cons; eauto.
  Qed.

  Lemma Forall_to_sig_NoDup l HPl : NoDup l → NoDup (Forall_to_sig l HPl).
  Proof.
    revert HPl; induction l as [|a l IHl]; simpl;
      intros HPl; first by constructor.
    inversion 1; inversion HPl; simplify_eq.
    constructor; last by apply IHl.
    intros ?%elem_of_Forall_to_sig_1; done.
  Qed.

  Lemma in_gset_finite (g : gset A) : (∀ x, P x → x ∈ g) → Finite {x : A | P x}.
  Proof.
    intros Hg.
    assert (Forall P (filter P (elements g))) as Hels.
    { apply Forall_forall. intros ?; rewrite elem_of_list_filter; tauto. }
    refine {| enum := Forall_to_sig (filter P (elements g)) Hels |}.
    - apply Forall_to_sig_NoDup. apply NoDup_filter. apply NoDup_elements.
    - intros x.
      edestruct (elem_of_Forall_to_sig_2 _ Hels) as [Hx' ?].
      { apply elem_of_list_filter; split; first apply (proj2_sig x).
        apply elem_of_elements, Hg; apply (proj2_sig x). }
      replace x with (`x ↾ Hx'); last by apply sig_eq.
      done.
  Qed.

End in_gset_finite.

Section in_list_finite.
  Context `{!EqDecision A}.
  Context {P : A → Prop} `{!∀ x : A, ProofIrrel (P x)}.

  Local Instance: ∀ x, Decision (P x).
  Proof. intros ?; apply make_decision. Qed.

  Lemma in_list_finite (l : list A) : (∀ x, P x → x ∈ l) → Finite {x : A | P x}.
  Proof.
    intros Hl.
    assert (Forall P (filter P (remove_dups l))) as Hels.
    { apply Forall_forall. intros ?; rewrite elem_of_list_filter; tauto. }
    refine {| enum := Forall_to_sig (filter P (remove_dups l)) Hels |}.
    - apply Forall_to_sig_NoDup. apply NoDup_filter, NoDup_remove_dups.
    - intros x.
      edestruct (elem_of_Forall_to_sig_2 _ Hels) as [Hx' ?].
      { apply elem_of_list_filter; split; first apply (proj2_sig x).
        apply elem_of_remove_dups, Hl; apply (proj2_sig x). }
      replace x with (`x ↾ Hx'); last by apply sig_eq.
      done.
  Qed.

End in_list_finite.

Require Import Coq.Logic.Epsilon.
Require Import Coq.Sorting.Permutation.

Section finite_range_gmap.
  Context `{!EqDecision K, !Countable K}.

  Definition set_choose_L' (X: gset K) (Hne: X ≠ ∅): { k : K | k ∈ X } :=
    constructive_indefinite_description _ (set_choose_L X Hne).

  Fixpoint enumerate_gmaps (D: list K) (N: nat) : list (gmap K nat) :=
    match D with
    | [] => [ ∅ ]
    | k::ks =>
        m1 ← enumerate_gmaps ks N;
        new ← seq 0 (N+1);
        mret (<[ k := new ]> m1)
  end.

  Local Instance all_the_instances A (P: A -> Prop) : ∀ x, Decision (P x).
  Proof. intros ?; apply make_decision. Qed.

  Lemma enumerate_gmaps_spec N l D m :
    elements D ≡ₚ l ∧ dom m = D ∧
             map_Forall (λ (_ : K) (v : nat), v ≤ N) m → m ∈ enumerate_gmaps l N.
  Proof.
    revert l D m.
    induction l; intros D m.

    { simpl. intros (Hel&Hl&?). eapply list.Permutation_nil_r in Hel. apply elements_empty_inv in Hel.
      rewrite leibniz_equiv_iff in Hel. rewrite Hel in *.
      apply dom_empty_inv_L in Hl as ->. set_solver. }
    simpl. intros (Hel & Hl & Hbound).

    assert (Hdecomp: ∃ m1 m2, m = m1 ∪ m2 ∧ dom m1 = {[a]} ∧ dom m2 = list_to_set l).
    { assert (list_to_set (elements D) = (list_to_set (a :: l): gset _)).
      { by rewrite Hel. }
      rewrite list_to_set_elements_L in H. simpl in H. rewrite <-Hl in H.
      apply dom_union_inv_L in H as (m1&m2&Hunion&Hmdisj&[Hdom1 Hdom2]); eauto.
      assert (a ∉ l); last set_solver.
      assert (NoDup (a :: l)).
      - rewrite <-Hel. apply NoDup_elements.
      - by apply NoDup_cons_1_1. }

    destruct Hdecomp as (m1&m2&Hunion&Hdom1&Hdom2). rewrite Hunion in *.
    assert (Hanotin: a ∉ dom m2).
    { rewrite Hdom2, elem_of_list_to_set.
      apply NoDup_cons_1_1. rewrite <-Hel. apply NoDup_elements. }
    apply dom_singleton_inv_L in Hdom1 as [v ->].
    apply elem_of_list_bind. exists m2; split; last first.
    - apply (IHl (dom m2)). repeat split.
      + rewrite <-Hl in Hel. rewrite dom_union in Hel.
        rewrite dom_singleton in Hel.
        rewrite elements_union_singleton in Hel; last done.
        by eapply Permutation_cons_inv.
      + eapply map_Forall_union_1_2; eauto.
        apply map_disjoint_singleton_l_2. by apply not_elem_of_dom.
    - apply elem_of_list_bind. exists v; split; last first.
      { specialize (Hbound a v). rewrite <-insert_union_singleton_l, lookup_insert in Hbound.
        specialize (Hbound eq_refl).
        apply elem_of_seq. split; lia. }
      rewrite insert_union_singleton_l. set_solver.
  Qed.

  Local Instance proof_irrel_P D N (m: gmap K nat):
    ProofIrrel (dom m = D ∧ map_Forall (λ _ v, v <= N) m).
  Proof. apply make_proof_irrel. Qed.

  Lemma bounded_maps_finite (D: gset K) (N : nat):
    Finite { m : gmap K nat | dom m = D ∧ map_Forall (λ _ v, v <= N) m}.
  Proof.
    apply (in_list_finite (enumerate_gmaps (elements D) N)).
    intros **. by eapply enumerate_gmaps_spec.
  Qed.

  Definition enum_gmap_bounded (D: gset K) (N : nat): list (gmap K nat) :=
    enumerate_gmaps (elements D) N.

  Lemma enum_gmap_bounded_spec N D m:
    dom m = D ∧ map_Forall (λ (_ : K) (v : nat), v ≤ N) m → m ∈ enum_gmap_bounded D N.
  Proof.
    intros **. unfold enum_gmap_bounded. eapply enumerate_gmaps_spec; done.
  Qed.

  Lemma enum_gmap_dom N D:
    Forall (λ m, dom m = D) (enum_gmap_bounded D N).
  Proof.
    assert (Hok: forall l D,
      elements D ≡ₚ l -> Forall (λ m, dom m = D) (enumerate_gmaps l N)
    ); last first.
    { rewrite Forall_forall. setoid_rewrite Forall_forall in Hok. by apply Hok. }
    induction l.
    { intros ? Hp. eapply list.Permutation_nil_r in Hp. eauto. apply elements_empty_inv in Hp.
      rewrite leibniz_equiv_iff in Hp. rewrite Hp. simpl. by rewrite Forall_singleton, dom_empty_L. }
    clear D. intros D Hel. simpl. rewrite Forall_forall. intros m Hin.
    apply elem_of_list_bind in Hin as (m'&Hin&Hin').

    assert (list_to_set (elements D) = (list_to_set (a :: l): gset _)).
    { by rewrite Hel. }
    rewrite list_to_set_elements_L in H. simpl in H.
    rewrite H in Hel. rewrite elements_union_singleton in Hel; last first.
    { rewrite elem_of_list_to_set. apply NoDup_cons_1_1. rewrite <-Hel.
      apply NoDup_elements. }

    apply Permutation_cons_inv in Hel; eauto.
    setoid_rewrite Forall_forall in IHl. specialize (IHl (list_to_set l) Hel _ Hin').

    rewrite H.
    apply elem_of_list_bind in Hin as (?&Hfin&Hseq).
    apply elem_of_list_singleton in Hfin as ->.
    rewrite dom_insert_L, IHl. done.
  Qed.

  Definition enum_gmap_bounded' (D: gset K) (N : nat): list { m : (gmap K nat) | dom m = D }:=
    Forall_to_sig _ (enum_gmap_dom N D).

  Lemma enum_gmap_bounded'_spec N D m Hdom:
    dom m = D ∧ map_Forall (λ (_ : K) (v : nat), v ≤ N) m → m ↾ Hdom ∈ enum_gmap_bounded' D N.
  Proof.
    intros * H. apply enum_gmap_bounded_spec,
                (elem_of_Forall_to_sig_2 _ (enum_gmap_dom N D)) in H as [Hdom' ?].
    assert (Hdom = Hdom') as -> by apply ProofIrrelevance. done.
  Qed.

End finite_range_gmap.

Section finite_range_gmap.
  Context {A : Type}.
  Context `{!EqDecision K, !Countable K, !EqDecision A}.

  Fixpoint enumerate_range_gmaps (D: list K) (lr: list A) : list (gmap K A) :=
    match D with
    | [] => [ ∅ ]
    | k::ks =>
        m1 ← enumerate_range_gmaps ks lr;
        new ← lr;
        mret (<[ k := new ]> m1)
  end.

  Local Instance all_the_range_instances B (P: B -> Prop) : ∀ x, Decision (P x).
  Proof. intros ?; apply make_decision. Qed.

  Lemma enumerate_range_gmaps_spec l lr D m:
    elements D ≡ₚ l ∧ dom m = D ∧
             map_Forall (λ (_ : K) (v : A), v ∈ lr) m → m ∈ enumerate_range_gmaps l lr.
  Proof.
    revert l D m.
    induction l; intros D m.

    { simpl. intros (Hel&Hl&?). eapply list.Permutation_nil_r in Hel. apply elements_empty_inv in Hel.
      rewrite leibniz_equiv_iff in Hel. rewrite Hel in *.
      apply dom_empty_inv_L in Hl as ->. set_solver. }
    simpl. intros (Hel & Hl & Hbound).

    assert (Hdecomp: ∃ m1 m2, m = m1 ∪ m2 ∧ dom m1 = {[a]} ∧ dom m2 = list_to_set l).
    { assert (list_to_set (elements D) = (list_to_set (a :: l): gset _)).
      { by rewrite Hel. }
      rewrite list_to_set_elements_L in H. simpl in H. rewrite <-Hl in H.
      apply dom_union_inv_L in H as (m1&m2&Hunion&Hmdisj&[Hdom1 Hdom2]); eauto.
      assert (a ∉ l); last set_solver.
      assert (NoDup (a :: l)).
      - rewrite <-Hel. apply NoDup_elements.
      - by apply NoDup_cons_1_1. }

    destruct Hdecomp as (m1&m2&Hunion&Hdom1&Hdom2). rewrite Hunion in *.
    assert (Hanotin: a ∉ dom m2).
    { rewrite Hdom2, elem_of_list_to_set.
      apply NoDup_cons_1_1. rewrite <-Hel. apply NoDup_elements. }
    apply dom_singleton_inv_L in Hdom1 as [v ->].
    apply elem_of_list_bind. exists m2; split; last first.
    - apply (IHl (dom m2)). repeat split.
      + rewrite <-Hl in Hel. rewrite dom_union in Hel.
        rewrite dom_singleton in Hel.
        rewrite elements_union_singleton in Hel; last done.
        by eapply Permutation_cons_inv.
      + eapply map_Forall_union_1_2; eauto.
        apply map_disjoint_singleton_l_2. by apply not_elem_of_dom.
    - apply elem_of_list_bind. exists v; split; last first.
      { specialize (Hbound a v). rewrite <-insert_union_singleton_l, lookup_insert in Hbound.
        by specialize (Hbound eq_refl). }
      rewrite insert_union_singleton_l. set_solver.
  Qed.

  Definition enum_range_prop D (lr : list A) :=
    fun (m: gmap K A) => dom m = D ∧ map_Forall (λ _ v, v ∈ lr) m. 
    
  Local Instance proof_irrel_range_P D (lr : list A) (m: gmap K A):
    ProofIrrel (enum_range_prop D lr m).
  Proof. apply make_proof_irrel. Qed.

  Lemma bounded_range_maps_finite (D: gset K) (lr: list A):
    Finite { m : gmap K A | enum_range_prop D lr m}.
  Proof.
    apply (in_list_finite (enumerate_range_gmaps (elements D) lr)).
    intros **. by eapply enumerate_range_gmaps_spec.
  Qed.

  Definition enum_gmap_range_bounded (D: gset K) (lr : list A): list (gmap K A) :=
    enumerate_range_gmaps (elements D) lr.

  Lemma enum_gmap_range_bounded_spec D m (lr : list A):
    enum_range_prop D lr m → m ∈ enum_gmap_range_bounded D lr.
  Proof.
    intros **. unfold enum_gmap_range_bounded. eapply enumerate_range_gmaps_spec; done.
  Qed.

  Lemma enum_gmap_range_dom lr D:
    Forall (enum_range_prop D lr) (enum_gmap_range_bounded D lr).
  Proof.
    assert (Hok: forall l D,
      elements D ≡ₚ l -> Forall (enum_range_prop D lr) (enumerate_range_gmaps l lr)
    ); last first.
    { rewrite Forall_forall. setoid_rewrite Forall_forall in Hok. by apply Hok. }
    induction l.
    { intros ? Hp. eapply list.Permutation_nil_r in Hp. eauto. apply elements_empty_inv in Hp.
      rewrite leibniz_equiv_iff in Hp. rewrite Hp. simpl.
      rewrite Forall_singleton. split.
      - set_solver.
      - apply map_Forall_empty. }
    clear D. intros D Hel. simpl. rewrite Forall_forall. intros m Hin.
    apply elem_of_list_bind in Hin as (m'&Hin&Hin').

    assert (list_to_set (elements D) = (list_to_set (a :: l): gset _)).
    { by rewrite Hel. }
    rewrite list_to_set_elements_L in H. simpl in H.
    rewrite H in Hel. rewrite elements_union_singleton in Hel; last first.
    { rewrite elem_of_list_to_set. apply NoDup_cons_1_1. rewrite <-Hel.
      apply NoDup_elements. }

    apply Permutation_cons_inv in Hel; eauto.
    setoid_rewrite Forall_forall in IHl. specialize (IHl (list_to_set l) Hel _ Hin') as [DOM CODOM]. 

    rewrite H.
    apply elem_of_list_bind in Hin as (?&Hfin&Hseq).    
    apply elem_of_list_singleton in Hfin as ->.
    split. 
    - rewrite dom_insert_L, DOM. done.
    - eapply map_Forall_insert_2; eauto. 
  Qed.

  Definition enum_gmap_range_bounded' (D: gset K) (lr : list A):
    list { m : (gmap K A) | enum_range_prop D lr m }
    := Forall_to_sig _ (enum_gmap_range_dom lr D).

  Lemma enum_gmap_range_bounded'_spec lr D m Hdom:
    enum_range_prop D lr m → m ↾ Hdom ∈ enum_gmap_range_bounded' D lr.
  Proof.
    intros * H. apply enum_gmap_range_bounded_spec,
                (elem_of_Forall_to_sig_2 _ (enum_gmap_range_dom lr D)) in H as [Hdom' ?].
    assert (Hdom = Hdom') as -> by apply ProofIrrelevance. done.
  Qed.

End finite_range_gmap.


Section enumerate_gsets.
  Context {A : Type}.
  Context `{!EqDecision A, !Countable A}.

  Fixpoint enumerate_dom_gsets (D: list A) : list (gset A) :=
    match D with
    | [] => [ ∅ ]
    | k::ks =>
        s_wo ← enumerate_dom_gsets ks;
        b ← [ true; false];
        if (b : bool) then mret s_wo else mret $ {[ k ]} ∪ s_wo
  end.

  Definition enumerate_dom_gsets' (D: gset A) : list (gset A) :=
    enumerate_dom_gsets (elements D).

  Local Instance all_the_range_instances' B (P: B -> Prop) : ∀ x, Decision (P x).
  Proof. intros ?; apply make_decision. Qed.

  Lemma enumerate_gsets_spec D l m :
    elements D ≡ₚ l ∧ m ⊆ D → m ∈ enumerate_dom_gsets l.
  Proof.
    revert l D m.
    induction l; intros D m.

    { simpl. intros (Hel&Hl). eapply list.Permutation_nil_r in Hel. apply elements_empty_inv in Hel.
      rewrite leibniz_equiv_iff in Hel. rewrite Hel in *. assert (m = ∅); set_solver. }
    simpl. intros (Hel & Hl).

    assert (Hdecomp: ∃ m1 m2, m = m1 ∪ m2 ∧ m1 ⊆ {[a]} ∧ m2 ⊆ list_to_set l).
    { assert (list_to_set (elements D) = (list_to_set (a :: l): gset _)).
      { by rewrite Hel. }
      rewrite list_to_set_elements_L in H. simpl in H. exists (m ∩ {[a]}), (m ∩ list_to_set l).
      split; last split; [set_solver|set_solver|set_solver]. }

    destruct Hdecomp as (m1&m2&Hunion&Hdom1&Hdom2). rewrite Hunion in *.
    assert (Hanotin: a ∉ m2).
    { intros contra. eapply elem_of_subseteq in contra; eauto. rewrite elem_of_list_to_set in contra.
      assert (a ∉ l); last done. apply NoDup_cons_1_1. rewrite <-Hel. apply NoDup_elements. }
    apply elem_of_list_bind. exists m2; split; last first.
    - apply (IHl (list_to_set l)). split; last set_solver. apply elements_list_to_set.
      eapply (NoDup_cons_1_2 a). rewrite <-Hel. apply NoDup_elements.
    - destruct (decide (a ∈ m1)).
      + assert (m1 = {[a]}) by set_solver. simplify_eq. set_solver.
      + assert (m1 = ∅) by set_solver. simplify_eq. rewrite union_empty_l_L. set_solver.
  Qed.

  Lemma enumerate_dom_gsets'_spec D s:
    s ⊆ D → s ∈ enumerate_dom_gsets' D.
  Proof.
    intros H. unfold enumerate_dom_gsets'. eapply (enumerate_gsets_spec D). split; set_solver.
  Qed.
End enumerate_gsets.
