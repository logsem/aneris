From Coq.ssr Require Import ssreflect.
From stdpp Require Import gmap.
From aneris.prelude Require Import gset_map.

Section sig_gset.
  Context `{EqDecision A, !Countable A}.

  (* TODO: upstream? *)
  Lemma length_elements (X : gset A) : length (elements X) = size X.
  Proof.
    induction X using set_ind_L.
    - rewrite elements_empty size_empty //.
    - rewrite size_union ?size_singleton; [set_solver|].
      rewrite elements_union_singleton //.
  Qed.

  Definition sig_gset (X : gset A) : Type := { a : A | a ∈ X }.

  Program Fixpoint sig_gset_list (X : gset A) (l : list A)
          (Hl : ∀ a, a ∈ l → a ∈ X) : list (sig_gset X) :=
    match l as l' return (∀ a, a ∈ l' → a ∈ X) → list { a : A | a ∈ X } with
    | [] => λ _, []
    | a :: l' => λ H, (a ↾ (H a _)) :: sig_gset_list X l' (λ b Hb, H b _)
    end Hl.
  Next Obligation. constructor. Qed.
  Next Obligation. by constructor. Qed.

  Lemma elem_of_sig_gset_list_lookup X l i (x : sig_gset X) H :
    sig_gset_list X l H !! i = Some x ↔ l !! i = Some (`x).
  Proof.
    revert i; induction l; [done|]. split.
    - destruct i; [by intros [= <-]|]. apply IHl.
    - destruct i; [|by apply IHl].
      intros [= ->]=> /=. f_equal.
      destruct x; simpl. f_equal. apply proof_irrel.
  Qed.

  Lemma length_sig_gset_list X l H :
    length (sig_gset_list X l H) = length l.
  Proof. induction l; naive_solver. Qed.

  Lemma sig_gset_list_proof_irrel X l H1 H2 :
    sig_gset_list X l H1 = sig_gset_list X l H2.
  Proof.
    induction l as [|?? IH]; [done|].
    simpl. f_equal; [|apply IH].
    f_equal. apply proof_irrel.
  Qed.

  Lemma sig_gset_list_cons X a l H :
    ∃ Ha Hl, sig_gset_list X (a :: l) H = a ↾ Ha :: sig_gset_list X l Hl.
  Proof.
    assert (∀ a, a ∈ l → a ∈ X) as Hl by set_solver.
    exists (H a (elem_of_list_here _ _)), Hl.
    simpl. f_equal; [| apply sig_gset_list_proof_irrel].
    f_equal. apply proof_irrel.
  Qed.

  Lemma sig_gset_list_singleton_list a X H :
    ∃ Ha, sig_gset_list X [a] H = [a ↾ Ha].
  Proof.
    exists (H a (elem_of_list_here _ _)).
    simpl. do 2 f_equal. apply proof_irrel.
  Qed.

  Lemma sig_gset_list_singleton_set a l H :
    l = [a] → ∃ Ha, sig_gset_list {[a]} l H = [a ↾ Ha].
  Proof. intros ->. eexists (H a _). simpl. do 2 f_equal. Qed.

  Program Definition sig_gset_gset (X : gset A) : gset (sig_gset X) :=
    list_to_set (C := gset _) (sig_gset_list X (elements X) _).
  Next Obligation. intros ??. by apply elem_of_elements. Qed.

  Lemma elem_of_sig_gset_gset X a :
    a ∈ sig_gset_gset X ↔ `a ∈ X.
  Proof.
    destruct a. split; [done|].
    intros [i ?]%elem_of_elements%elem_of_list_lookup_1.
    rewrite /sig_gset_gset elem_of_list_to_set.
    apply (elem_of_list_lookup_2 _ i).
    by apply elem_of_sig_gset_list_lookup.
  Qed.

  Lemma sig_gset_gset_singleton a :
    ∃ Ha, sig_gset_gset {[a]} = {[a ↾ Ha]}.
  Proof.
    assert (a ∈ ({[a]} : gset _)) as Ha by set_solver.
    eexists Ha. apply set_eq. intros ?.
    rewrite elem_of_sig_gset_gset //.
  Qed.

  Lemma sig_gset_gset_empty :
    sig_gset_gset ∅ = ∅.
  Proof. done. Qed.

  Lemma size_sig_gset X :
    size X = size (sig_gset_gset X).
  Proof.
    rewrite /sig_gset_gset -length_elements.
    refine ((fix IH l H (Hnodup : NoDup l) :=
               match l as l' return
                     l = l' →
                     NoDup l' →
                     ∀ (H : ∀ x, x ∈ l' → x ∈ _),
                       length l' =
                       size (list_to_set (sig_gset_list X l' H)) with
               | [] => _
               | a :: l' => _
               end eq_refl Hnodup H) (elements X) _ _).
    - intros -> ??. rewrite size_empty //.
    - intros -> Hd ?. inversion Hd; simplify_eq.
      edestruct sig_gset_list_cons as [? [? ->]].
      simpl. rewrite size_union ?size_singleton ?IH //.
      rewrite disjoint_singleton_l.
      rewrite elem_of_list_to_set.
      intros [? Hl']%elem_of_list_lookup_1.
      by apply elem_of_sig_gset_list_lookup, elem_of_list_lookup_2 in Hl'.
    - apply NoDup_elements.
  Qed.

  Lemma sig_gset_map_proj1_sig_subseteq (X : gset A) (Y : gset (sig_gset X)) :
    gset_map proj1_sig Y ⊆ X.
  Proof. set_unfold. by intros ? ([] & -> &?). Qed.

End sig_gset.

#[global] Hint Extern 1 ((`?p) ∈ _) => apply (proj2_sig p) : core.
#[global] Hint Extern 1 (_ ∈ sig_gset_gset _) => apply elem_of_sig_gset_gset : core.
